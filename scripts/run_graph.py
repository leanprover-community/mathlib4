#!/usr/bin/env python3
"""Minimal reference executor for Lake v2 graph manifests.

Intentionally simple: load the v2 JSON, topo-order the requested target's
subgraph, and invoke each node's `command` in sequence. No CAS, no caching,
no scheduler, no parallelism. The whole point is that a passing
`validate-outputs` diff attributes correctness to the *graph extractor*,
not to executor cleverness.

If you want a real scheduler, this file is the wrong abstraction — use the
graph JSON as input to Bazel, BuildBuddy, or your own queue.

Usage
-----
    run_graph.py <manifest.json> [--target <module>] [--only|--missing]

Options
-------
    --target <module>   Only execute the subgraph reachable from <module>.
                        Default: all nodes (target field of the graph).
    --only              Execute only the target node (skip deps).
    --missing           Execute only nodes whose outputs don't exist.
    --clean             rm -rf every output directory before running.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Iterable


def _absolutize(s: str, ctx: list[tuple[str, str]]) -> str:
    """Inverse of lake_graph_extract's relativization."""
    for var, value in ctx:
        token = f"${var}"
        if s == token:
            return value
        if s.startswith(token + "/"):
            return value + s[len(token):]
    return s


def _absolutize_argv(argv: list[str], ctx: list[tuple[str, str]]) -> list[str]:
    """Like _absolutize but supports @<path> rsp args."""
    out: list[str] = []
    for s in argv:
        if s.startswith("@"):
            out.append("@" + _absolutize(s[1:], ctx))
        else:
            out.append(_absolutize(s, ctx))
    return out


def _topo_subgraph_order(
    nodes_by_id: dict[str, dict],
    target_id: str | None,
) -> list[str]:
    """Return node IDs in topo order; restrict to target's transitive deps if set."""
    mod_to_id: dict[str, str] = {}
    for nid, n in nodes_by_id.items():
        if n.get("kind") == "lean_module":
            mod_to_id[n["module"]] = nid
    
    if target_id is None:
        # All nodes in manifest order (already topo-sorted by Lake)
        return list(nodes_by_id.keys())
    
    if target_id in nodes_by_id:
        seed_id = target_id
    elif target_id in mod_to_id:
        seed_id = mod_to_id[target_id]
    else:
        raise ValueError(f"Target {target_id!r} not found in graph")
    
    # BFS from seed to collect transitive deps
    visited: set[str] = set()
    queue: list[str] = [seed_id]
    while queue:
        nid = queue.pop(0)
        if nid in visited:
            continue
        visited.add(nid)
        node = nodes_by_id[nid]
        # Collect deps (import_arts for lean_module nodes list modules)
        for (dep_mod, _) in node.get("import_arts", []):
            if dep_mod in mod_to_id:
                dep_id = mod_to_id[dep_mod]
                if dep_id not in visited:
                    queue.append(dep_id)
    
    # Return in manifest order (preserves topo order)
    return [nid for nid in nodes_by_id.keys() if nid in visited]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("manifest", help="Path to v2 manifest JSON")
    parser.add_argument("--target", default=None,
                        help="Target module/exe name (default: graph's target field)")
    parser.add_argument("--only", action="store_true",
                        help="Execute only the target node, skip deps")
    parser.add_argument("--missing", action="store_true",
                        help="Execute only nodes with missing outputs")
    parser.add_argument("--clean", action="store_true",
                        help="rm -rf all output directories before running")
    
    args = parser.parse_args()
    
    manifest_path = Path(args.manifest)
    if not manifest_path.exists():
        print(f"Manifest not found: {manifest_path}", file=sys.stderr)
        return 1
    
    manifest = json.loads(manifest_path.read_text())
    
    # Build indices
    nodes = manifest["nodes"]
    nodes_by_id: dict[str, dict] = {n["id"]: n for n in nodes}
    mod_to_node_id: dict[str, str] = {}
    for n in nodes:
        if n.get("kind") == "lean_module":
            mod_to_node_id[n["module"]] = n["id"]
    
    # Determine target
    target_id = args.target or manifest.get("target")
    if target_id and target_id in mod_to_node_id:
        target_id = mod_to_node_id[target_id]
    
    # Get execution order
    if args.only:
        exec_ids = [target_id] if target_id and target_id in nodes_by_id else []
    else:
        exec_ids = _topo_subgraph_order(nodes_by_id, target_id)
    
    # Build context for absolutization
    ws = manifest["workspace"]
    ctx = [
        ("LAKE_HOME", ws["LAKE_HOME"]),
        ("WORKSPACE", ws["WORKSPACE"]),
        ("TOOLCHAIN", ws["TOOLCHAIN"]),
        ("TOOLCHAIN_ROOT", ws.get("TOOLCHAIN_ROOT", str(Path(ws["TOOLCHAIN"]).parent))),
    ]
    
    # Clean if requested
    if args.clean:
        for nid in exec_ids:
            node = nodes_by_id[nid]
            for out in node["outputs"]:
                p = Path(_absolutize(out, ctx))
                if p.exists():
                    if p.is_dir():
                        shutil.rmtree(p)
                    else:
                        p.unlink()
    
    # Execute
    print(f"Executing {len(exec_ids)} nodes")
    for i, nid in enumerate(exec_ids):
        node = nodes_by_id[nid]
        
        # Skip if outputs exist and --missing is set
        if args.missing:
            all_exist = all(Path(_absolutize(out, ctx)).exists() for out in node["outputs"])
            if all_exist:
                print(f"  [{i+1}/{len(exec_ids)}] SKIP {nid} (outputs exist)")
                continue
        
        print(f"  [{i+1}/{len(exec_ids)}] RUN {nid}")
        
        cmd = _absolutize_argv(node["command"], ctx)
        env = os.environ.copy()
        if "env" in node:
            node_env = {k: _absolutize(v, ctx) for k, v in node["env"].items()}
            env.update(node_env)
        
        # For lean_module nodes with setup.json, write it first
        if node.get("kind") == "lean_module" and "import_arts" in node:
            # Reconstruct setup.json from import_arts
            setup_path_rel = None
            for out in node["outputs"]:
                if out.endswith(".setup.json"):
                    setup_path_rel = out
                    break
            
            if setup_path_rel:
                setup_path = Path(_absolutize(setup_path_rel, ctx))
                setup_path.parent.mkdir(parents=True, exist_ok=True)
                
                # Build setup.json content
                modules = manifest.get("modules", {})
                importArts_dict = {}
                for (mname, importAll) in node["import_arts"]:
                    if mname in modules:
                        me = modules[mname]
                        if not me.get("isModule", False):
                            arts = [me["olean"]]
                        elif importAll:
                            arts = [me["olean"], me["ir"], me.get("oleanServer", ""), me.get("oleanPrivate", "")]
                        else:
                            arts = [me["olean"], me["ir"], me.get("oleanServer", "")]
                        importArts_dict[mname] = arts
                
                setup_json = {
                    "name": node["module"],
                    "package": modules.get(node["module"], {}).get("package", ""),
                    "isModule": modules.get(node["module"], {}).get("isModule", True),
                    "importArts": importArts_dict,
                    "dynlibs": [],
                    "plugins": [],
                    "options": modules.get(node["module"], {}).get("leanOptions", {}),
                }
                
                setup_path.write_text(json.dumps(setup_json))
        
        # Ensure output directories exist
        for out in node["outputs"]:
            p = Path(_absolutize(out, ctx))
            p.parent.mkdir(parents=True, exist_ok=True)
        
        # Run command
        res = subprocess.run(cmd, env=env, cwd=Path(ws["WORKSPACE"]))
        if res.returncode != 0:
            print(f"  FAILED with exit code {res.returncode}", file=sys.stderr)
            return 1
    
    print(f"All {len(exec_ids)} nodes executed successfully")
    return 0


if __name__ == "__main__":
    sys.exit(main())
