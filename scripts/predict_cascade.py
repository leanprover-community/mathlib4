#!/usr/bin/env python3
"""
Usage: predict_cascade.py <import_graph.dot> <changed_files.txt>

Prints the number of Mathlib modules that a change to the listed files
rebuilds: the changed modules and every module that imports one of them,
directly or transitively.

`import_graph.dot` is the output of `lake exe graph` at the merge-base: an
edge `"A" -> "B"` means that module `B` imports module `A`. The changed files
are paths relative to the repository root, one per line. A file that is not
a Mathlib module, or a module that is new and so is not in the graph,
counts as one module.

A change to `lakefile.lean`, `lake-manifest.json` or `lean-toolchain`
rebuilds every module, so the count is then the number of modules in the
graph.
"""

import re
import sys
from collections import defaultdict

EDGE = re.compile(r'^\s*"([^"]+)"\s*->\s*"([^"]+)"')
NODE = re.compile(r'^\s*"([^"]+)"\s*\[')
REBUILD_ALL = {"lakefile.lean", "lake-manifest.json", "lean-toolchain"}


def read_graph(path):
    dependents = defaultdict(set)
    modules = set()
    with open(path, encoding="utf-8") as f:
        for line in f:
            m = EDGE.match(line)
            if m:
                dependents[m.group(1)].add(m.group(2))
                modules.update(m.groups())
                continue
            m = NODE.match(line)
            if m:
                modules.add(m.group(1))
    return dependents, modules


def module_name(path):
    if not (path.startswith("Mathlib/") and path.endswith(".lean")):
        return None
    return path[: -len(".lean")].replace("/", ".")


def main():
    dependents, modules = read_graph(sys.argv[1])
    with open(sys.argv[2], encoding="utf-8") as f:
        changed = [line.strip() for line in f if line.strip()]
    if any(path in REBUILD_ALL for path in changed):
        print(len(modules))
        return
    seen = set()
    stack = [m for m in map(module_name, changed) if m is not None]
    while stack:
        mod = stack.pop()
        if mod in seen:
            continue
        seen.add(mod)
        stack.extend(dependents.get(mod, ()))
    print(len(seen))


if __name__ == "__main__":
    main()
