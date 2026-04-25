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
        return _absolutize(obj, ctx)
    if isinstance(obj, list):
        return [_absolutize_obj(x, ctx) for x in obj]
    if isinstance(obj, dict):
        return {k: _absolutize_obj(v, ctx) for k, v in obj.items()}
    return obj


def _topo_subgraph_order(
    nodes_by_id: dict[str, dict],
    target_id: str | None,
) -> list[str]:
    """Return node IDs in topo order; if ``target_id`` is set, restrict to its
    transitive build dependencies (plus the target itself)."""
    # We trust the input ordering (lake_graph_extract emits topo-ordered),
    # we just filter to the target's closure if requested.
    pkg_module_to_id: dict[str, str] = {}
    for nid, n in nodes_by_id.items():
        if n.get("kind") == "lean_module":
            pkg_module_to_id[n["module"]] = nid

    if target_id is None:
        return list(nodes_by_id.keys())

    if target_id in nodes_by_id:
        seed_id = target_id
    elif target_id in pkg_module_to_id:
        seed_id = pkg_module_to_id[target_id]
    else:
        raise KeyError(
            f"target {target_id!r} is not a node id or known module"
        )

    # BFS over graph_deps (which use module names, not ids) to find the
    # closure. graph_deps were emitted from setup_json importArts which only
    # cover lean_module nodes, so module-name lookup is sufficient.
    closure_ids: set[str] = set()
    queue = [seed_id]
    while queue:
        nid = queue.pop()
        if nid in closure_ids:
            continue
        closure_ids.add(nid)
        node = nodes_by_id[nid]
        for dep_module in node.get("graph_deps", []):
            dep_id = pkg_module_to_id.get(dep_module)
            if dep_id is not None and dep_id not in closure_ids:
                queue.append(dep_id)

    # Preserve the input file's order for the subset (which is topological).
    return [nid for nid in nodes_by_id.keys() if nid in closure_ids]


def execute_node(node: dict, ctx: list[tuple[str, str]]) -> None:
    """Run one graph node's command after writing its setup.json."""
    abs_command = _absolutize_list(node["command"], ctx)
    abs_env = {k: _absolutize(v, ctx) for k, v in node["env"].items()}

    # Write setup.json. We absolutize *its* paths too, so the on-disk file
    # matches what Lake would have produced.
    setup_path_rel = _find_setup_path_in_outputs(node)
    if setup_path_rel is not None:
        setup_path = _absolutize(setup_path_rel, ctx)
        setup_content = _absolutize_obj(node["setup_json"], ctx)
        Path(setup_path).parent.mkdir(parents=True, exist_ok=True)
        # Lake writes setup.json with `(toJson setup).pretty` — its exact
        # whitespace differs from Python's, but the JSON content is what
        # `lean --setup` reads, so semantic equivalence suffices.
        Path(setup_path).write_text(json.dumps(setup_content, indent=1))

    # Pre-create output directories the command itself doesn't auto-create.
    for out_rel in node["outputs"]:
        Path(_absolutize(out_rel, ctx)).parent.mkdir(parents=True, exist_ok=True)

    # Subprocess env is the caller's env extended with the node's env.
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
    args = parser.parse_args(argv)

    graph = json.loads(args.graph_json.read_text())
    ws = graph["workspace"]
    ctx = [
        ("LAKE_HOME", ws["LAKE_HOME"]),
        ("WORKSPACE", ws["WORKSPACE"]),
        ("TOOLCHAIN", ws["TOOLCHAIN"]),
    ]

    nodes_by_id = {n["id"]: n for n in graph["nodes"]}

    target = args.target if args.target is not None else graph.get("target")
    order = _topo_subgraph_order(nodes_by_id, target)

    if args.only:
        # Strip back to just the target node. The closure-walk above gives us
        # the right node id even if `target` was supplied as a module name.
        target_id = order[-1] if order else None
        order = [target_id] if target_id is not None else []

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
