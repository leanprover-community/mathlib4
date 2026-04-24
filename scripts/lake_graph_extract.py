#!/usr/bin/env python3
"""Extract mathlib4's Lake build graph as a static (command, inputs, outputs) DAG.

See lake_build_graph_analysis.md for the design rationale. This is the v0:
single-module emission + command-level validation. Larger scope (whole project,
output-level validation, cc_compile/cc_link nodes) lives in subsequent versions.

v0 strategy
-----------
Workspace-uniform constants (LEAN_PATH, toolchain path, packages list) are
captured empirically once and treated as static. Per-module variability
(transitive imports, source path, output paths, setup.json) is derived. The
setup.json *content* is currently obtained from ``lake setup-file <M>`` as an
oracle: it is the field most likely to drift if upstream packages change, and
v0 wants to validate the command template independently of the setup-derivation
logic. v1 will replace the oracle with static derivation from the lakefile +
import graph and will diff its output against the oracle as a regression test.

Sub-commands
------------
- emit            : write a single-module node to stdout (debugging aid)
- validate-commands <module> : run ``lake build -v`` on the module and byte-diff
                                the captured trace against the extracted command

Path conventions (relativized in emitted JSON; absolutized for validation)
-------------------------------------------------------------------------
$WORKSPACE   : project root (e.g. /Users/chelo/mathlib4)
$LAKE_HOME   : $WORKSPACE/.lake (cache, packages)
$TOOLCHAIN   : the toolchain bin dir derived from ``lake env lean``
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
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

# --- Workspace constants (captured empirically; verified by --validate-commands)

WORKSPACE = Path("/Users/chelo/mathlib4").resolve()
LAKE_HOME = WORKSPACE / ".lake"
PACKAGES_DIR = LAKE_HOME / "packages"

# Order observed in `lake build -v` LEAN_PATH (see lake_build_graph_analysis.md
# §5.1, §5.3 and the Mathlib.Init capture). LEAN_PATH is workspace-static —
# every module of every package gets the same one. The order is Lake's
# topological resolution; rather than re-implement it we lift it verbatim.
LEAN_PATH_PACKAGES = [
    "Cli",                # transitive (via importGraph)
    "batteries",          # direct mathlib deps in lakefile order:
    "Qq",
    "aesop",
    "proofwidgets",
    "importGraph",
    "LeanSearchClient",
    "plausible",
]

# Lean libraries declared in mathlib's lakefile.lean (see §5 of the analysis)
# plus the upstream packages' lakefile.tomls. Each entry says:
#   pkg_dir : where the package lives ("" = mathlib root, "<name>" = .lake/packages/<name>)
#   srcDir  : the package-relative source directory (default: "")
#   leanOptions : the canonical options dict (oracle-fetched once per lib)
@dataclass
class LibConfig:
    pkg: str           # "mathlib" or upstream package name
    name: str          # lean_lib name
    pkg_dir: Path      # absolute pkg dir (mathlib root or .lake/packages/<pkg>)
    src_dir: Path      # absolute source root (= pkg_dir / srcDir)
    build_dir: Path    # absolute .lake/build dir for this package


def package_dirs() -> dict[str, Path]:
    """Return map pkg-name -> absolute package directory."""
    out: dict[str, Path] = {"mathlib": WORKSPACE}
    for child in sorted(PACKAGES_DIR.iterdir()) if PACKAGES_DIR.exists() else []:
        if child.is_dir():
            out[child.name] = child
    return out


def find_module_source(
    module: str, packages: dict[str, Path],
) -> tuple[str, Path]:
    """Locate ``module``'s source file across all packages.

    Returns (pkg_name, absolute_src_path). Mathlib is searched first so its
    own modules win (none of mathlib's lean_libs use a non-default srcDir).
    Raises FileNotFoundError if the module's source can't be found.
    """
    rel = module_to_relpath(module)
    # mathlib first
    candidate = packages["mathlib"] / rel
    if candidate.is_file():
        return "mathlib", candidate
    # then upstream packages, in deterministic order
    for pkg_name, pkg_dir in packages.items():
        if pkg_name == "mathlib":
            continue
        candidate = pkg_dir / rel
        if candidate.is_file():
            return pkg_name, candidate
    raise FileNotFoundError(
        f"Could not locate source for module {module!r} under "
        f"{', '.join(str(p) for p in packages.values())}"
    )


# ---------------------------------------------------------------------------
# Toolchain discovery
# ---------------------------------------------------------------------------

def discover_lean_binary() -> Path:
    """Resolve the lean binary that ``lake env`` would invoke."""
    res = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=WORKSPACE, capture_output=True, text=True, check=True,
    )
    # `lean --version` prints e.g. "Lean (version 4.30.0-rc2, ...)" — we don't
    # actually parse it; we just need the *path* to the binary, which we ask
    # the shell to find via `lake env`.
    res = subprocess.run(
        ["lake", "env", "sh", "-c", "command -v lean"],
        cwd=WORKSPACE, capture_output=True, text=True, check=True,
    )
    return Path(res.stdout.strip())


# ---------------------------------------------------------------------------
# Path helpers (module name <-> filesystem)
# ---------------------------------------------------------------------------

def module_to_relpath(module: str) -> Path:
    """``Mathlib.Init`` -> ``Mathlib/Init.lean`` (suffix added by caller)."""
    return Path(*module.split(".")).with_suffix(".lean")


# ---------------------------------------------------------------------------
# setup-file oracle
# ---------------------------------------------------------------------------

def lake_setup_file(module_lean_path: Path) -> dict:
    """Return the parsed setup.json that ``lake setup-file <p>`` produces.

    `module_lean_path` must be a path Lake recognizes. For mathlib's own
    modules pass the relative path (e.g. ``Mathlib/Init.lean``); for upstream
    pass the absolute path under .lake/packages.
    """
    res = subprocess.run(
        ["lake", "setup-file", str(module_lean_path)],
        cwd=WORKSPACE, capture_output=True, text=True, check=True,
    )
    return json.loads(res.stdout)


# ---------------------------------------------------------------------------
# Per-package lean_lib discovery (parsing what we strictly need)
# ---------------------------------------------------------------------------

def parse_mathlib_lakefile_libs() -> dict[str, dict]:
    """Return name -> {srcDir, root, globs, leanOptions_canonical=None}.

    We do not elaborate Lake; we read literal declarations from the source.
    leanOptions are filled in later via lake setup-file.
    """
    text = (WORKSPACE / "lakefile.lean").read_text()
    libs: dict[str, dict] = {}
    # crude but sufficient — mathlib's lakefile is regular
    for match in re.finditer(
        r"lean_lib\s+(?:\W*)([A-Za-z_][A-Za-z_0-9]*|«[^»]+»)\s+where\b([^\n]*(?:\n(?![a-zA-Z@/]).*)*)",
        text,
    ):
        raw_name = match.group(1)
        name = raw_name.strip("«»")
        body = match.group(2)
        libs[name] = {"raw": body}
    return libs


# ---------------------------------------------------------------------------
# Build an extracted node for a single module
# ---------------------------------------------------------------------------

@dataclass
class ExtractedNode:
    id: str
    kind: str  # "lean_module" for v0
    command: list[str]
    env: dict[str, str]
    inputs: list[dict]   # [{path, sha256?}]
    outputs: list[str]
    setup_json: dict


def _abs_path(p: str | Path) -> str:
    return str(Path(p).resolve())


def lean_path_string(packages: dict[str, Path]) -> str:
    """Build the ':'-joined LEAN_PATH for a mathlib module build."""
    parts: list[str] = []
    for pkg_name in LEAN_PATH_PACKAGES:
        if pkg_name not in packages:
            raise RuntimeError(
                f"Expected package '{pkg_name}' under {PACKAGES_DIR} "
                f"(LEAN_PATH order is empirically captured; if a package was "
                f"renamed/removed re-capture via `lake build -v`)"
            )
        parts.append(str(packages[pkg_name] / ".lake" / "build" / "lib" / "lean"))
    parts.append(str(WORKSPACE / ".lake" / "build" / "lib" / "lean"))
    return ":".join(parts)


def lean_module_node(
    module: str,
    *,
    lean_bin: Path,
    packages: dict[str, Path],
) -> ExtractedNode:
    """Build the node for a Lean module in any package."""
    pkg_name, src = find_module_source(module, packages)
    pkg_dir = packages[pkg_name]
    rel = module_to_relpath(module)

    # `lake setup-file` accepts either an absolute path or a workspace-relative
    # path. Absolute always works regardless of which package the module lives in.
    setup = lake_setup_file(src)

    lib_dir = pkg_dir / ".lake" / "build" / "lib" / "lean"
    ir_dir = pkg_dir / ".lake" / "build" / "ir"

    olean       = lib_dir / rel.with_suffix(".olean")
    ilean       = lib_dir / rel.with_suffix(".ilean")
    olean_srv   = lib_dir / rel.with_suffix(".olean.server")
    olean_priv  = lib_dir / rel.with_suffix(".olean.private")
    ir          = lib_dir / rel.with_suffix(".ir")
    c           = ir_dir  / rel.with_suffix(".c")
    setup_path  = ir_dir  / rel.with_suffix(".setup.json")

    command = [
        str(lean_bin),
        str(src),
        "-o", str(olean),
        "-i", str(ilean),
        "-c", str(c),
        "--setup", str(setup_path),
        "--json",
    ]
    env = {"LEAN_PATH": lean_path_string(packages)}

    # v0 inputs: source + setup.json + transitive importArts (paths only; sha256
    # left empty — populated when CAS-ready emission is added).
    inputs: list[dict] = [{"path": str(src)}, {"path": str(setup_path)}]
    for art_module, paths in setup.get("importArts", {}).items():
        for p in paths:
            inputs.append({"path": p, "module": art_module})

    outputs = [
        str(olean), str(ilean), str(olean_srv), str(olean_priv),
        str(ir), str(c), str(setup_path),
    ]
    if setup.get("isModule"):
        # already covered above; module-style adds .olean.server, .olean.private, .ir
        pass

    return ExtractedNode(
        id=f"{pkg_name}:{module}",
        kind="lean_module",
        command=command,
        env=env,
        inputs=inputs,
        outputs=outputs,
        setup_json=setup,
    )


# ---------------------------------------------------------------------------
# Validation: run lake build -v, capture trace, diff
# ---------------------------------------------------------------------------

TRACE_PREFIX = "trace: .> "

def _capture_lake_trace_for_module(module: str) -> str:
    """Force a rebuild of `module` and return its `trace: .>` argv line.

    The module's olean+sidecars are deleted first so Lake actually re-invokes
    `lean`; otherwise it would `Replay` the cached artifact and emit no trace.
    Works for cross-package modules — artifacts are deleted in the *owning*
    package's build dir.
    """
    packages = package_dirs()
    pkg_name, src = find_module_source(module, packages)
    pkg_dir = packages[pkg_name]
    rel = module_to_relpath(module)
    lib = pkg_dir / ".lake" / "build" / "lib" / "lean"
    ir  = pkg_dir / ".lake" / "build" / "ir"
    base_lib_stem = rel.with_suffix("").name  # e.g. "Init"
    base_ir_stem = base_lib_stem
    for d, base in [(lib / rel.parent, base_lib_stem),
                    (ir  / rel.parent, base_ir_stem)]:
        if not d.exists():
            continue
        for f in d.iterdir():
            if f.name == base or f.name.startswith(base + "."):
                f.unlink()

    res = subprocess.run(
        ["lake", "build", module, "-v"],
        cwd=WORKSPACE, capture_output=True, text=True,
    )
    if res.returncode != 0:
        raise RuntimeError(f"lake build {module} failed:\n{res.stdout}\n{res.stderr}")

    abs_src = str(src)
    for line in res.stdout.splitlines():
        if not line.startswith(TRACE_PREFIX):
            continue
        argv = line[len(TRACE_PREFIX):]
        if abs_src in argv:
            return argv
    raise RuntimeError(
        f"No trace: .> line for {module} in lake output. Captured "
        f"{sum(1 for l in res.stdout.splitlines() if l.startswith(TRACE_PREFIX))} "
        f"trace lines total."
    )


def _argv_from_trace(trace_argv: str) -> tuple[dict[str, str], list[str]]:
    """Parse a ``LEAN_PATH=... lean ...`` trace into (env, argv).

    Lake emits exactly one env var (LEAN_PATH) followed by the binary and args.
    No quoting or shell metacharacters appear in mathlib paths.
    """
    parts = trace_argv.split(" ")
    env: dict[str, str] = {}
    i = 0
    while i < len(parts) and "=" in parts[i] and not parts[i].startswith("/"):
        k, _, v = parts[i].partition("=")
        env[k] = v
        i += 1
    return env, parts[i:]


def validate_commands(module: str) -> int:
    """Run lake-build for the module and diff its argv against our extraction."""
    lean_bin = discover_lean_binary()
    packages = package_dirs()
    node = lean_module_node(module, lean_bin=lean_bin, packages=packages)

    trace = _capture_lake_trace_for_module(module)
    actual_env, actual_argv = _argv_from_trace(trace)

    expected_env = node.env
    expected_argv = node.command

    print(f"=== validate-commands: {module} ===")
    diffs: list[str] = []

    # env diff
    for k in sorted(set(expected_env) | set(actual_env)):
        e = expected_env.get(k); a = actual_env.get(k)
        if e != a:
            diffs.append(f"env[{k}]: expected={e!r} actual={a!r}")

    # argv diff
    if expected_argv != actual_argv:
        for i, (e, a) in enumerate(zip(expected_argv, actual_argv)):
            if e != a:
                diffs.append(f"argv[{i}]: expected={e!r} actual={a!r}")
        if len(expected_argv) != len(actual_argv):
            diffs.append(
                f"argv length: expected={len(expected_argv)} actual={len(actual_argv)}"
            )

    if diffs:
        print("MISMATCH:")
        for d in diffs:
            print(f"  {d}")
        return 1

    print("MATCH")
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="lake_graph_extract")
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_emit = sub.add_parser("emit", help="emit a single-module node JSON to stdout")
    p_emit.add_argument("module")

    p_val = sub.add_parser(
        "validate-commands",
        help="run lake build -v on a module and diff against the extracted command",
    )
    p_val.add_argument("module")

    args = parser.parse_args(argv)

    if args.cmd == "emit":
        lean_bin = discover_lean_binary()
        packages = package_dirs()
        node = lean_module_node(args.module, lean_bin=lean_bin, packages=packages)
        json.dump(
            {
                "id": node.id,
                "kind": node.kind,
                "command": node.command,
                "env": node.env,
                "inputs_count": len(node.inputs),
                "outputs": node.outputs,
                "setup_json_keys": sorted(node.setup_json.keys()),
            },
            sys.stdout, indent=2,
        )
        sys.stdout.write("\n")
        return 0

    if args.cmd == "validate-commands":
        return validate_commands(args.module)

    parser.error(f"unknown subcommand: {args.cmd}")
    return 2


if __name__ == "__main__":
    sys.exit(main())
