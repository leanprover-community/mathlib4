#!/usr/bin/env python3
"""Minimal reference executor for build graphs emitted by lake_graph_extract.py.

Intentionally simple: load the JSON, topo-order the requested target's
subgraph, and invoke each node's ``command`` in sequence. No CAS, no caching,
no scheduler, no parallelism. The whole point is that a passing
``--validate-outputs`` diff attributes correctness to the *graph extractor*,
not to executor cleverness.

If you want a real scheduler, this file is the wrong abstraction — use the
graph JSON as input to Bazel, BuildBuddy, or your own queue.

Usage
-----
    run_graph.py <build_graph.json> [--target <module>] [--clean]

Options
-------
    --target <module>   Only execute the subgraph reachable from <module>.
                        Default: all nodes (target field of the graph).
    --clean             ``rm -rf`` every output directory under the workspace
                        before running. Required for the ``validate-outputs``
                        sanity check to be meaningful (so we know nothing was
                        already on disk).
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
    """Inverse of lake_graph_extract.relativize. Same prefix-priority order."""
    for var, value in ctx:
        token = f"${var}"
        if s == token:
            return value
        if s.startswith(token + "/"):
            return value + s[len(token):]
    return s


def _absolutize_list(seq: Iterable[str], ctx: list[tuple[str, str]]) -> list[str]:
    return [_absolutize(s, ctx) for s in seq]


def _absolutize_obj(obj, ctx: list[tuple[str, str]]):
    if isinstance(obj, str):
        if obj.startswith("@"):
            return "@" + _absolutize(obj[1:], ctx)
        return _absolutize(obj, ctx)
    if isinstance(obj, list):
        return [_absolutize_obj(x, ctx) for x in obj]
    if isinstance(obj, dict):
        return {k: _absolutize_obj(v, ctx) for k, v in obj.items()}
    return obj


def _absolutize_argv(argv: list[str], ctx: list[tuple[str, str]]) -> list[str]:
    """Like _absolutize_list but supports ``@<path>`` rsp args."""
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
    """Return node IDs in topo order; if ``target_id`` is set, restrict to its
    transitive build dependencies (plus the target itself)."""
    pkg_module_to_id: dict[str, str] = {}
    exe_name_to_id: dict[str, str] = {}
    for nid, n in nodes_by_id.items():
        if n.get("kind") == "lean_module":
            pkg_module_to_id[n["module"]] = nid
        if n.get("kind") == "cc_link":
            # cc_link is the ultimate root of an exe build; prefer it over
            # the lean_module of the same name when resolving an exe target.
            exe_name_to_id[n["exe_name"]] = nid

    if target_id is None:
        return list(nodes_by_id.keys())

    if target_id in nodes_by_id:
        seed_id = target_id
    elif target_id in exe_name_to_id:
        seed_id = exe_name_to_id[target_id]
    elif target_id in pkg_module_to_id:
        seed_id = pkg_module_to_id[target_id]
    else:
        raise KeyError(
            f"target {target_id!r} is not a node id, exe name, or known module"
        )

    # BFS over graph_deps. graph_deps may be either node ids (cc_compile /
    # cc_link emit them as ids) OR module names (lean_module emits the
    # module-name list from setup_json.importArts). Look up both.
    closure_ids: set[str] = set()
    queue = [seed_id]
    while queue:
        nid = queue.pop()
        if nid in closure_ids:
            continue
        closure_ids.add(nid)
        node = nodes_by_id[nid]
        for dep in node.get("graph_deps", []):
            dep_id = (
                dep if dep in nodes_by_id
                else pkg_module_to_id.get(dep)
            )
            if dep_id is not None and dep_id not in closure_ids:
                queue.append(dep_id)

    return [nid for nid in nodes_by_id.keys() if nid in closure_ids]


def execute_node(node: dict, ctx: list[tuple[str, str]]) -> None:
    """Run one graph node's command after writing any side-input files.

    Side-inputs handled by the executor (vs the node's command):
      * setup.json — for ``lean_module`` nodes, written from
        ``node['setup_json']``. ``lean --setup`` reads it before compiling.
      * .rsp — for ``cc_link`` nodes, written from ``node['rsp_args']`` in
        Lake's quoted-line format.
    """
    abs_command = _absolutize_argv(node["command"], ctx)
    abs_env = {k: _absolutize(v, ctx) for k, v in node["env"].items()}

    # 1. setup.json side-input for lean_module nodes.
    setup_path_rel = _find_setup_path_in_outputs(node)
    if setup_path_rel is not None and "setup_json" in node:
        setup_path = _absolutize(setup_path_rel, ctx)
        setup_content = _absolutize_obj(node["setup_json"], ctx)
        Path(setup_path).parent.mkdir(parents=True, exist_ok=True)
        # Lake writes setup.json with `(toJson setup).pretty`; the exact
        # whitespace differs from Python's, but the JSON content is what
        # `lean --setup` reads, so semantic equivalence suffices.
        Path(setup_path).write_text(json.dumps(setup_content, indent=1))

    # 2. .rsp side-input for cc_link nodes. Lake's mkArgs writes one quoted
    #    arg per line, with backslash-escaping of '\' and '"'.
    if node.get("kind") == "cc_link":
        rsp_path = _absolutize(node["rsp_path"], ctx)
        rsp_args_abs = _absolutize_list(node["rsp_args"], ctx)
        Path(rsp_path).parent.mkdir(parents=True, exist_ok=True)
        with open(rsp_path, "w") as f:
            for arg in rsp_args_abs:
                escaped = arg.replace("\\", "\\\\").replace('"', '\\"')
                f.write(f'"{escaped}"\n')

    # Pre-create output directories the command itself doesn't auto-create.
    for out_rel in node["outputs"]:
        Path(_absolutize(out_rel, ctx)).parent.mkdir(parents=True, exist_ok=True)

    env = os.environ.copy()
    env.update(abs_env)

    res = subprocess.run(abs_command, env=env, capture_output=True, text=True)
    if res.returncode != 0:
        sys.stderr.write(
            f"[run_graph] node {node['id']} failed (exit {res.returncode})\n"
        )
        sys.stderr.write(res.stdout)
        sys.stderr.write(res.stderr)
        raise SystemExit(res.returncode)


def _find_setup_path_in_outputs(node: dict) -> str | None:
    for out in node["outputs"]:
        if out.endswith(".setup.json"):
            return out
    return None


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("graph_json", type=Path)
    parser.add_argument("--target", default=None,
                        help="restrict execution to this target's transitive closure")
    parser.add_argument(
        "--clean", action="store_true",
        help="rm -rf .lake/build trees before executing (required for validate-outputs)",
    )
    parser.add_argument(
        "--only", action="store_true",
        help="execute only the target node, not its transitive build deps "
             "(assumes deps are already built on disk; useful for single-node "
             "validation)",
    )
    parser.add_argument(
        "--missing", action="store_true",
        help="execute only nodes whose declared outputs aren't all already on "
             "disk (incremental mode; useful for partial-rebuild validation)",
    )
    args = parser.parse_args(argv)

    graph = json.loads(args.graph_json.read_text())
    ws = graph["workspace"]
    # Order matters: most-specific prefix first for absolutize. TOOLCHAIN
    # (= <root>/bin) must come before TOOLCHAIN_ROOT.
    ctx = [
        ("LAKE_HOME", ws["LAKE_HOME"]),
        ("WORKSPACE", ws["WORKSPACE"]),
        ("TOOLCHAIN", ws["TOOLCHAIN"]),
        ("TOOLCHAIN_ROOT", ws.get("TOOLCHAIN_ROOT", str(Path(ws["TOOLCHAIN"]).parent))),
    ]

    nodes_by_id = {n["id"]: n for n in graph["nodes"]}

    target = args.target if args.target is not None else graph.get("target")
    order = _topo_subgraph_order(nodes_by_id, target)

    if args.only:
        # Strip back to just the target node. The closure-walk above gives us
        # the right node id even if `target` was supplied as a module name.
        target_id = order[-1] if order else None
        order = [target_id] if target_id is not None else []

    if args.missing:
        order = [
            nid for nid in order
            if not all(
                Path(_absolutize(o, ctx)).exists() for o in nodes_by_id[nid]["outputs"]
            )
        ]
        sys.stderr.write(f"[run_graph] --missing: {len(order)} nodes need rebuild\n")

    if args.clean:
        # Wipe .lake/build for every package referenced by these nodes — that
        # is, every output's parent .lake/build/ tree. Detect by walking up
        # from each output path until we hit ``.lake/build``.
        cleaned: set[Path] = set()
        for nid in order:
            for out in nodes_by_id[nid]["outputs"]:
                abs_out = Path(_absolutize(out, ctx))
                cur = abs_out
                while cur.parent != cur:
                    if cur.name == "build" and cur.parent.name == ".lake":
                        if cur not in cleaned:
                            cleaned.add(cur)
                            if cur.exists():
                                shutil.rmtree(cur)
                        break
                    cur = cur.parent
        sys.stderr.write(f"[run_graph] cleaned: {len(cleaned)} build trees\n")

    sys.stderr.write(f"[run_graph] executing {len(order)} nodes\n")
    for i, nid in enumerate(order, 1):
        node = nodes_by_id[nid]
        sys.stderr.write(f"[run_graph] [{i}/{len(order)}] {nid}\n")
        execute_node(node, ctx)
    sys.stderr.write("[run_graph] done\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
