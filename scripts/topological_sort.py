#!/usr/bin/env python3
"""Print Mathlib modules in topological (import-DAG) order.

If filenames or module names are provided on stdin, outputs only those modules
in topological order; otherwise outputs all modules.

By default modules are printed leaves-last: if A imports B, then B appears
before A. Use --reverse for leaves-first order.

TODO: import-graph should come with this feature.
"""

import argparse
import sys
from pathlib import Path

from dag_traversal import DAG


def main():
    parser = argparse.ArgumentParser(
        description="Print Mathlib modules in topological order.",
    )
    parser.add_argument(
        "--reverse", action="store_true",
        help="Leaves first (if A imports B, A appears before B)",
    )
    args = parser.parse_args()

    dag = DAG.from_directories(Path("."))
    levels = dag.levels_backward()
    if not args.reverse:
        levels = levels[::-1]
    sorted_modules = [m for level in levels for m in level]

    # Optionally filter to modules listed on stdin.
    if not sys.stdin.isatty():
        input_modules = set()
        for line in sys.stdin:
            line = line.strip()
            if not line:
                continue
            if line.endswith(".lean"):
                # Convert file path (Mathlib/Foo/Bar.lean) to module name.
                input_modules.add(".".join(Path(line).with_suffix("").parts))
            else:
                input_modules.add(line)
        if input_modules:
            sorted_modules = [m for m in sorted_modules if m in input_modules]

    for module in sorted_modules:
        print(module)


if __name__ == "__main__":
    main()
