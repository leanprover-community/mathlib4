#!/usr/bin/env python3
"""
Demote every top-level markdown header beyond the first one in Lean docstrings.

This script ensures that each `.lean` file in the repository contains at most one `# Heading`
inside docstrings by rewriting any subsequent `#` headings as `##`.
"""
from __future__ import annotations

import argparse
import re
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple

HEADER_RE = re.compile(r"^\s*#(?!#)(?=\s|$)")
SKIP_DIRS = {".git", ".lake", "build", "Cache"}


def should_skip(path: Path) -> bool:
    """Return True if the path is inside a directory we should skip."""
    return any(part in SKIP_DIRS for part in path.parts)


def iter_docstrings(text: str) -> Iterable[Tuple[int, int]]:
    """Yield (start, end) byte offsets for each `/-! ... -/` docstring, handling nesting."""
    stack: List[Tuple[bool, int]] = []
    i = 0
    length = len(text)
    while i < length - 1:
        tri = text[i : i + 3]
        if tri.startswith("/-!"):
            stack.append((True, i))
            i += 3
            continue
        bi = tri[:2]
        if bi == "/-":
            stack.append((False, i))
            i += 2
            continue
        if bi == "-/":
            if stack:
                is_doc, start = stack.pop()
                if is_doc:
                    yield (start, i + 2)
            i += 2
            continue
        i += 1


def rewrite_docstring(block: str, seen_header: bool) -> Tuple[str, bool, bool]:
    """
    Rewrite a single docstring, demoting headers after the first seen in the file.

    Returns (new_block, new_seen_header, changed?).
    """
    assert block.startswith("/-!")
    assert block.endswith("-/")
    inner = block[3:-2]
    lines = inner.splitlines(keepends=True) or [inner]
    changed = False
    for idx, line in enumerate(lines):
        match = HEADER_RE.match(line)
        if match:
            if seen_header:
                # Insert an extra `#` after the matched whitespace.
                lines[idx] = line[: match.end() - 1] + "##" + line[match.end() :]
                changed = True
            else:
                seen_header = True
    new_inner = "".join(lines)
    if not lines:  # ensure empty docstrings are preserved exactly
        new_inner = inner
    return "/-!" + new_inner + "-/", seen_header, changed


def rewrite_file(path: Path) -> bool:
    """Rewrite `path` in-place; return True if anything changed."""
    text = path.read_text(encoding="utf-8")
    doc_ranges = list(iter_docstrings(text))
    if not doc_ranges:
        return False
    pieces: List[str] = []
    cursor = 0
    seen_header = False
    changed = False
    for start, end in doc_ranges:
        pieces.append(text[cursor:start])
        new_block, seen_header, block_changed = rewrite_docstring(text[start:end], seen_header)
        pieces.append(new_block)
        changed = changed or block_changed
        cursor = end
    pieces.append(text[cursor:])
    if changed:
        path.write_text("".join(pieces), encoding="utf-8")
    return changed


def collect_files(root: Path, files: Sequence[Path] | None) -> List[Path]:
    """Return the list of `.lean` files to process."""
    if files:
        return [path for path in files if path.suffix == ".lean" and not should_skip(path)]
    results: List[Path] = []
    for path in sorted(root.rglob("*.lean")):
        if should_skip(path):
            continue
        results.append(path)
    return results


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "paths",
        nargs="*",
        type=Path,
        help="Optional list of `.lean` files to rewrite. Defaults to the whole repo.",
    )
    args = parser.parse_args()
    repo_root = Path(__file__).resolve().parents[1]
    files = collect_files(repo_root, args.paths)
    changed_files = 0
    for file in files:
        if rewrite_file(file):
            changed_files += 1
    print(f"Updated {changed_files} files.")


if __name__ == "__main__":
    main()
