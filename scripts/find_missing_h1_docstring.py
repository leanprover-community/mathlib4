#!/usr/bin/env python3
"""
Flag Lean files that have no H1 header in any docstring.

A docstring is recognized as a block comment starting with `/--` or `/-!`.
An H1 header is recognized as a line matching `# <text>` (exactly one `#`).
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path


H1_RE = re.compile(r"^\s*#(?!#)\s+\S")


def has_h1_header(docstring: str) -> bool:
    return any(H1_RE.match(line) for line in docstring.splitlines())


def extract_docstrings(text: str) -> list[str]:
    docstrings: list[str] = []
    block_stack: list[tuple[bool, int]] = []
    in_string = False
    i = 0
    n = len(text)

    while i < n:
        if block_stack:
            if text.startswith("/--", i):
                block_stack.append((True, i + 3))
                i += 3
            elif text.startswith("/-!", i):
                block_stack.append((True, i + 3))
                i += 3
            elif text.startswith("/-", i):
                block_stack.append((False, -1))
                i += 2
            elif text.startswith("-/", i):
                is_doc, start = block_stack.pop()
                if is_doc and start >= 0:
                    docstrings.append(text[start:i])
                i += 2
            else:
                i += 1
            continue

        if in_string:
            if text[i] == "\\":
                i += 2
            elif text[i] == '"':
                in_string = False
                i += 1
            else:
                i += 1
            continue

        if text.startswith("--", i):
            newline = text.find("\n", i)
            if newline == -1:
                break
            i = newline + 1
        elif text.startswith("/--", i):
            block_stack.append((True, i + 3))
            i += 3
        elif text.startswith("/-!", i):
            block_stack.append((True, i + 3))
            i += 3
        elif text.startswith("/-", i):
            block_stack.append((False, -1))
            i += 2
        elif text[i] == '"':
            in_string = True
            i += 1
        else:
            i += 1

    return docstrings


def file_has_h1_docstring(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    docstrings = extract_docstrings(text)
    return any(has_h1_header(docstring) for docstring in docstrings)


def default_lean_files() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "*.lean"],
        check=True,
        capture_output=True,
        text=True,
    )
    return [Path(line) for line in result.stdout.splitlines() if line]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Flag Lean files with no H1 header in any docstring."
    )
    parser.add_argument(
        "paths",
        nargs="*",
        type=Path,
        help="Lean files to scan. Defaults to git-tracked *.lean files.",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print scanned file count and missing count.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    paths = args.paths or default_lean_files()
    lean_paths = [p for p in paths if p.suffix == ".lean"]

    missing_h1: list[Path] = []
    for path in lean_paths:
        if not path.exists():
            continue
        if not file_has_h1_docstring(path):
            missing_h1.append(path)

    for path in missing_h1:
        print(path.as_posix())

    if args.verbose:
        print(
            f"scanned {len(lean_paths)} Lean files; "
            f"{len(missing_h1)} missing H1 docstring headers",
            file=sys.stderr,
        )

    return 1 if missing_h1 else 0


if __name__ == "__main__":
    raise SystemExit(main())
