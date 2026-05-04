#!/usr/bin/env python3
"""Extract mathlib4's Lake build graph as a static (command, inputs, outputs) DAG.

v2 approach: consume Lake's native `lake graph-extract` v2 manifest output.
The manifest carries all graph shape (module metadata, import dependencies,
commands, artifacts) in a single JSON document. This tool provides validators
and a reference executor.

Sub-commands
------------
- validate-commands <module> : run `lake build -v` on the module and byte-diff
- validate-setup <module>    : semantic diff of setup.json vs lake setup-file
- validate-outputs <target>  : end-to-end: emit v2 -> rebuild -> compare artifacts

See lake_graph_extract.md for design details.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Optional

# --- Workspace constants (verified by validators)

WORKSPACE = Path("/Users/chelo/mathlib4").resolve()
LAKE_HOME = WORKSPACE / ".lake"
PACKAGES_DIR = LAKE_HOME / "packages"

# Lake binary (must point to the native v2-emitting binary)
LAKE_BIN = "/Users/chelo/mathlib4/lean4-src/tests/lake/.lake/build/bin/lake"


# --- V2 Manifest Loader ---

class V2ManifestLoader:
    """Load and query a v2 Lake graph-extract manifest.
    
    The manifest contains:
    - workspace: placeholder paths (WORKSPACE, LAKE_HOME, TOOLCHAIN, TOOLCHAIN_ROOT)
    - nodes: array of {id, kind, module, command, env, outputs, import_arts}
    - modules: dict of module_name -> {src, package, isModule, olean, ir, ...}
    """
    
    def __init__(self, manifest_path: Path):
        self.path = manifest_path
        self.manifest = json.loads(manifest_path.read_text())
        self.workspace = self.manifest["workspace"]
        self.modules = self.manifest["modules"]
        self.nodes_by_id = {n["id"]: n for n in self.manifest["nodes"]}
    
    def get_node_v1_shape(self, node_id: str) -> dict[str, Any]:
        """Reconstruct v1 node shape from v2 (for backwards compatibility).
        
        Reads a v2 node and reconstructs the full v1-style node with
        reconstructed setup_json and inputs list.
        """
        node = self.nodes_by_id[node_id]
        if node["kind"] != "lean_module":
            raise ValueError(f"Only lean_module nodes supported; got {node['kind']}")
        
        mod_name = node["module"]
        me = self.modules[mod_name]
        
        # Reconstruct inputs from import_arts
        inputs = [
            {"path": me["src"], "kind": "source"},
            {"path": me["setupJsonPath"], "kind": "setup_json"},
        ]
        
        importArts_dict = {}
        for (mname, importAll) in node["import_arts"]:
            ime = self.modules[mname]
            if not ime["isModule"]:
                arts = [ime["olean"]]
            elif importAll:
                arts = [ime["olean"], ime["ir"], ime["oleanServer"], ime["oleanPrivate"]]
            else:
                arts = [ime["olean"], ime["ir"], ime["oleanServer"]]
            importArts_dict[mname] = arts
            for a in arts:
                inputs.append({"path": a, "kind": "import_art", "module": mname})
        
        # Reconstruct setup_json
        setup_json = {
            "name": mod_name,
            "package": me["package"],
            "isModule": me["isModule"],
            "importArts": importArts_dict,
            "dynlibs": [],
            "plugins": [],
            "options": me.get("leanOptions", {}),
        }
        
        return {
            "id": node["id"],
            "kind": node["kind"],
            "module": mod_name,
            "command": node["command"],
            "env": node["env"],
            "inputs": inputs,
            "outputs": node["outputs"],
            "setup_json": setup_json,
            "graph_deps": sorted(m for (m, _) in node["import_arts"]),
        }


def absolutize(s: str, ctx: list[tuple[str, str]]) -> str:
    """Inverse of run_graph.py's relativization. Same prefix-priority order."""
    for var, value in ctx:
        token = f"${var}"
        if s == token:
            return value
        if s.startswith(token + "/"):
            return value + s[len(token):]
    return s


def absolutize_argv(argv: list[str], ctx: list[tuple[str, str]]) -> list[str]:
    """Like absolutize but preserves @ for rsp args."""
    out: list[str] = []
    for s in argv:
        if s.startswith("@"):
            out.append("@" + absolutize(s[1:], ctx))
        else:
            out.append(absolutize(s, ctx))
    return out


# --- Validators ---

def validate_commands(target: str) -> int:
    """Extract command for target and byte-diff against lake build -v trace."""
    manifest_path = Path(tempfile.mktemp(suffix=".json"))
    try:
        # Extract v2 manifest
        res = subprocess.run(
            [LAKE_BIN, "graph-extract", target, str(manifest_path)],
            capture_output=True, text=True, cwd=WORKSPACE,
        )
        if res.returncode != 0:
            print(f"graph-extract failed: {res.stderr}", file=sys.stderr)
            return 1
        
        loader = V2ManifestLoader(manifest_path)
        
        # Find the lean_module node for this target
        target_node = None
        for node in loader.manifest["nodes"]:
            if node["kind"] == "lean_module" and node["module"] == target:
                target_node = node
                break
        
        if not target_node:
            print(f"Module {target} not found in manifest", file=sys.stderr)
            return 1
        
        # Resolve placeholder paths
        ctx = [
            ("LAKE_HOME", loader.workspace["LAKE_HOME"]),
            ("WORKSPACE", loader.workspace["WORKSPACE"]),
            ("TOOLCHAIN", loader.workspace["TOOLCHAIN"]),
            ("TOOLCHAIN_ROOT", loader.workspace.get("TOOLCHAIN_ROOT",
                str(Path(loader.workspace["TOOLCHAIN"]).parent))),
        ]
        
        extracted_cmd = absolutize_argv(target_node["command"], ctx)
        extracted_env = {k: absolutize(v, ctx) for k, v in target_node["env"].items()}
        
        # Delete module outputs to force rebuild
        me = loader.modules[target]
        setup_path = absolutize(me["setupJsonPath"], ctx)
        for path_str in [me["olean"], me["ir"], me["oleanServer"], me["oleanPrivate"], setup_path]:
            p = Path(absolutize(path_str, ctx))
            if p.exists():
                p.unlink()
            # Delete sidecars
            for suf in [".hash", ".trace"]:
                sp = p.parent / (p.name + suf)
                if sp.exists():
                    sp.unlink()
        
        # Capture lake build -v trace
        env = os.environ.copy()
        env.update(extracted_env)
        res = subprocess.run(
            ["lake", "build", "-v", target],
            cwd=WORKSPACE, capture_output=True, text=True, env=env,
        )
        
        # Extract argv from trace (look for "lean" command line)
        # Lake's trace format: [#...] <command> <args...>
        trace_lines = res.stderr.split("\n")
        lake_cmd = None
        for line in trace_lines:
            if "lean" in line and "-o" in line:
                # Parse the bracketed command
                m = re.search(r'\[\#\d+\]\s+(.+)', line)
                if m:
                    # This is a simplified extraction; full version would use shlex
                    parts = m.group(1).split()
                    if parts[0].endswith("lean"):
                        lake_cmd = parts
                        break
        
        if not lake_cmd:
            print(f"Could not extract lean command from lake build -v", file=sys.stderr)
            return 1
        
        # Byte-diff extracted vs lake
        print(f"=== validate-commands: {target} ===")
        extracted_str = " ".join(extracted_cmd)
        lake_str = " ".join(lake_cmd)
        
        if extracted_str == lake_str:
            print("PASS: command matches")
            return 0
        else:
            print("FAIL: command mismatch")
            print(f"Extracted: {extracted_str}")
            print(f"Lake:      {lake_str}")
            return 1
    finally:
        if manifest_path.exists():
            manifest_path.unlink()


def validate_setup(target: str) -> int:
    """Semantic diff of reconstructed setup.json vs lake setup-file output."""
    manifest_path = Path(tempfile.mktemp(suffix=".json"))
    try:
        # Extract v2 manifest
        res = subprocess.run(
            [LAKE_BIN, "graph-extract", target, str(manifest_path)],
            capture_output=True, text=True, cwd=WORKSPACE,
        )
        if res.returncode != 0:
            print(f"graph-extract failed: {res.stderr}", file=sys.stderr)
            return 1
        
        loader = V2ManifestLoader(manifest_path)
        
        if target not in loader.modules:
            print(f"Module {target} not found in manifest", file=sys.stderr)
            return 1
        
        # Reconstruct setup.json from v2
        me = loader.modules[target]
        me_imported = []
        for node in loader.manifest["nodes"]:
            if node["kind"] == "lean_module" and node["module"] == target:
                me_imported = node["import_arts"]
                break
        
        importArts_dict = {}
        for (mname, importAll) in me_imported:
            ime = loader.modules[mname]
            if not ime["isModule"]:
                arts = [ime["olean"]]
            elif importAll:
                arts = [ime["olean"], ime["ir"], ime["oleanServer"], ime["oleanPrivate"]]
            else:
                arts = [ime["olean"], ime["ir"], ime["oleanServer"]]
            importArts_dict[mname] = arts
        
        reconstructed = {
            "name": target,
            "package": me["package"],
            "isModule": me["isModule"],
            "importArts": importArts_dict,
            "dynlibs": [],
            "plugins": [],
            "options": me.get("leanOptions", {}),
        }
        
        # Get lake's setup.json
        res = subprocess.run(
            ["lake", "setup-file", target],
            cwd=WORKSPACE, capture_output=True, text=True,
        )
        if res.returncode != 0:
            print(f"lake setup-file failed: {res.stderr}", file=sys.stderr)
            return 1
        
        lake_setup = json.loads(res.stdout)
        
        print(f"=== validate-setup: {target} ===")
        
        # Semantic comparison (sorted keys)
        recon_sorted = json.dumps(reconstructed, sort_keys=True)
        lake_sorted = json.dumps(lake_setup, sort_keys=True)
        
        if recon_sorted == lake_sorted:
            print("PASS: setup.json matches semantically")
            return 0
        else:
            print("FAIL: setup.json mismatch")
            print(f"Reconstructed keys: {sorted(reconstructed.keys())}")
            print(f"Lake keys: {sorted(lake_setup.keys())}")
            for k in set(reconstructed.keys()) & set(lake_setup.keys()):
                if reconstructed[k] != lake_setup[k]:
                    print(f"  Diff in {k}:")
                    print(f"    Reconstructed: {reconstructed[k]!r}")
                    print(f"    Lake:          {lake_setup[k]!r}")
            return 1
    finally:
        if manifest_path.exists():
            manifest_path.unlink()


def _is_diffable_output(path_str: str) -> bool:
    """Exclude sidecars from diff."""
    return not any(path_str.endswith(suf) for suf in [".hash", ".trace", ".rsp", ".setup.json"])


def _file_sha256(path: Path) -> str:
    """Compute SHA256 of file."""
    h = hashlib.sha256()
    with open(path, "rb") as f:
        h.update(f.read())
    return h.hexdigest()


def _delete_node_outputs(node_id: str, loader: V2ManifestLoader, ctx: list[tuple[str, str]]) -> int:
    """Delete outputs + sidecars for a node."""
    node = loader.nodes_by_id[node_id]
    deleted = 0
    for out_path in node["outputs"]:
        p = Path(absolutize(out_path, ctx))
        if p.exists():
            p.unlink()
            deleted += 1
        # Delete sidecars
        for suf in [".hash", ".trace"]:
            sp = p.parent / (p.name + suf)
            if sp.exists():
                sp.unlink()
                deleted += 1
    return deleted


def validate_outputs(target: str, full: bool = False) -> int:
    """End-to-end: extract manifest, rebuild, compare output hashes."""
    manifest_path = Path(tempfile.mktemp(suffix=".json"))
    try:
        # Extract v2 manifest
        res = subprocess.run(
            [LAKE_BIN, "graph-extract", target, str(manifest_path)],
            capture_output=True, text=True, cwd=WORKSPACE,
        )
        if res.returncode != 0:
            print(f"graph-extract failed: {res.stderr}", file=sys.stderr)
            return 1
        
        loader = V2ManifestLoader(manifest_path)
        
        ctx = [
            ("LAKE_HOME", loader.workspace["LAKE_HOME"]),
            ("WORKSPACE", loader.workspace["WORKSPACE"]),
            ("TOOLCHAIN", loader.workspace["TOOLCHAIN"]),
            ("TOOLCHAIN_ROOT", loader.workspace.get("TOOLCHAIN_ROOT",
                str(Path(loader.workspace["TOOLCHAIN"]).parent))),
        ]
        
        # Find nodes to check
        if full:
            nodes_to_check = [n["id"] for n in loader.manifest["nodes"]]
        else:
            nodes_to_check = [
                n["id"] for n in loader.manifest["nodes"]
                if n.get("kind") == "lean_module" and n.get("module") == target
            ]
        
        if not nodes_to_check:
            print(f"Target {target} not found in manifest", file=sys.stderr)
            return 1
        
        # Collect output paths to check
        outputs_abs: list[Path] = []
        for nid in nodes_to_check:
            node = loader.nodes_by_id[nid]
            for o in node["outputs"]:
                if _is_diffable_output(o):
                    outputs_abs.append(Path(absolutize(o, ctx)))
        
        # Golden hashes before rebuild
        golden: dict[Path, str] = {}
        missing_pre: list[Path] = []
        for p in outputs_abs:
            if p.exists():
                golden[p] = _file_sha256(p)
            else:
                missing_pre.append(p)
        
        mode = "full" if full else "single-target"
        print(f"=== validate-outputs ({mode}): {target} ===")
        print(f"nodes: {len(nodes_to_check)} outputs: {len(outputs_abs)} "
              f"golden: {len(golden)} missing: {len(missing_pre)}")
        
        # Delete outputs
        deleted = sum(_delete_node_outputs(nid, loader, ctx) for nid in nodes_to_check)
        print(f"deleted {deleted} files")
        
        # Rebuild via run_graph.py
        run_graph_path = Path(__file__).parent / "run_graph.py"
        run_args = [sys.executable, str(run_graph_path), str(manifest_path)]
        if not full:
            run_args.append("--only")
        
        res = subprocess.run(run_args, capture_output=True, text=True)
        if res.returncode != 0:
            print("run_graph.py FAILED")
            sys.stderr.write(res.stdout)
            sys.stderr.write(res.stderr)
            return 1
        
        print("run_graph.py: ok")
        
        # Compare hashes
        missing_post: list[Path] = []
        diffs: list[str] = []
        for p in outputs_abs:
            if not p.exists():
                missing_post.append(p)
                continue
            old_hash = golden.get(p)
            if old_hash is None:
                continue
            new_hash = _file_sha256(p)
            if new_hash != old_hash:
                diffs.append(f"  {p}\n    golden={old_hash}\n    rebuilt={new_hash}")
        
        if missing_post:
            print(f"MISSING after rebuild ({len(missing_post)}):")
            for p in missing_post[:5]:
                print(f"  {p}")
            if len(missing_post) > 5:
                print(f"  ... and {len(missing_post) - 5} more")
            return 1
        
        if diffs:
            print(f"HASH MISMATCHES ({len(diffs)}):")
            for d in diffs:
                print(d)
            return 1
        
        print("PASS: all outputs match")
        return 0
    finally:
        if manifest_path.exists():
            manifest_path.unlink()


# --- CLI ---

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="cmd", required=True)
    
    cmd_validate_commands = subparsers.add_parser(
        "validate-commands", help="Byte-diff extracted vs lake build -v command"
    )
    cmd_validate_commands.add_argument("module")
    
    cmd_validate_setup = subparsers.add_parser(
        "validate-setup", help="Semantic diff of setup.json"
    )
    cmd_validate_setup.add_argument("module")
    
    cmd_validate_outputs = subparsers.add_parser(
        "validate-outputs", help="End-to-end: rebuild and compare hashes"
    )
    cmd_validate_outputs.add_argument("target")
    cmd_validate_outputs.add_argument("--full", action="store_true",
                                      help="Rebuild entire closure")
    
    args = parser.parse_args()
    
    if args.cmd == "validate-commands":
        return validate_commands(args.module)
    elif args.cmd == "validate-setup":
        return validate_setup(args.module)
    elif args.cmd == "validate-outputs":
        return validate_outputs(args.target, args.full)
    
    return 1


if __name__ == "__main__":
    sys.exit(main())
