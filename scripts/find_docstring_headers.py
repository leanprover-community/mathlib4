#!/usr/bin/env python3
"""
Report Lean files whose docstrings contain more than one top-level markdown header.

A top-level markdown header is a line that starts with `#` (but not `##` or deeper)
inside a `/-! ... -/` docstring. The script walks every `.lean` file under the
repository root (or an optional user-provided directory) and lists the offenders.
"""
from __future__ import annotations

import re
import sys
from pathlib import Path
from typing import List, Tuple

HEADER_RE = re.compile(r"^\s*#(?!#)(?=\s|$)")
SKIP_DIRS = {".git", ".lake", "build", "Cache"}


def count_docstring_headers(text: str) -> int:
    """Return how many single-`#` headers appear across all docstrings in `text`."""
    stack: List[Tuple[bool, int | None]] = []
    count = 0
    i = 0
    length = len(text)

    while i < length - 1:
        chunk = text[i : i + 3]
        if chunk.startswith("/-!"):
            stack.append((True, i + 3))
            i += 3
            continue
        chunk = chunk[:2]
        if chunk == "/-":
            stack.append((False, None))
            i += 2
            continue
        if chunk == "-/":
            if stack:
                is_doc, start_idx = stack.pop()
                if is_doc and start_idx is not None:
                    docstring = text[start_idx:i]
                    count += sum(1 for line in docstring.splitlines() if HEADER_RE.match(line))
            i += 2
            continue
        i += 1

    return count


def should_skip(path: Path) -> bool:
    """Return True if the path is inside a skipped directory."""
    return any(part in SKIP_DIRS for part in path.parts)


def find_files_with_multiple_headers(root: Path) -> List[Tuple[Path, int]]:
    """Return (path, header_count) for Lean files that exceed one header."""
    results: List[Tuple[Path, int]] = []
    for path in sorted(root.rglob("*.lean")):
        if should_skip(path):
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        header_count = count_docstring_headers(text)
        if header_count > 1:
            results.append((path, header_count))
    return results


def main() -> None:
    search_root = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parents[1]
    offenders = find_files_with_multiple_headers(search_root)
    if not offenders:
        print("No Lean files found with more than one top-level docstring header.")
        return
    for path, header_count in offenders:
        try:
            rel_path = path.relative_to(search_root)
        except ValueError:
            rel_path = path
        print(f"{rel_path} ({header_count} headers)")


if __name__ == "__main__":
    main()
