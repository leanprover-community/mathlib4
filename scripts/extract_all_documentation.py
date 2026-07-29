#!/usr/bin/env python3
"""Extract comments from Mathlib's main source trees into a plain-text corpus.

This uses the same Lean-aware parser and prose cleanup as
``extract_measure_theory_documentation.py``. The default corpus covers ``Mathlib``, ``Archive``,
``Counterexamples``, and ``MathlibTest``.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import sys

from extract_measure_theory_documentation import REPOSITORY_ROOT, render_file


DEFAULT_SOURCE_ROOTS = (
    REPOSITORY_ROOT / "Mathlib",
    REPOSITORY_ROOT / "Archive",
    REPOSITORY_ROOT / "Counterexamples",
    REPOSITORY_ROOT / "MathlibTest",
)
DEFAULT_OUTPUT = REPOSITORY_ROOT / "docs" / "mathlib_comments.txt"


def build_corpus(source_roots: list[Path]) -> str:
    """Build a deterministic corpus for all Lean files below the selected source roots."""

    roots = [source_root.resolve() for source_root in source_roots]
    files = [
        (path, source_root)
        for source_root in roots
        for path in source_root.rglob("*.lean")
    ]
    files.sort(key=lambda entry: entry[0].as_posix())
    return "\n\n".join(render_file(path, source_root) for path, source_root in files) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source-root",
        type=Path,
        action="append",
        help="source directory to include; may be given more than once",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="generated corpus path (default: %(default)s)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if the output is missing or differs, without writing it",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    source_roots = args.source_root or list(DEFAULT_SOURCE_ROOTS)
    source_roots = [source_root.resolve() for source_root in source_roots]
    output = args.output.resolve()
    missing = [source_root for source_root in source_roots if not source_root.is_dir()]
    if missing:
        print(f"source root does not exist: {missing[0]}", file=sys.stderr)
        return 2

    try:
        corpus = build_corpus(source_roots)
    except ValueError as error:
        print(f"could not parse comments: {error}", file=sys.stderr)
        return 2

    if args.check:
        if not output.is_file() or output.read_text(encoding="utf-8") != corpus:
            print(f"{output} is stale; run {Path(__file__).name} to regenerate it", file=sys.stderr)
            return 1
        return 0

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(corpus, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
