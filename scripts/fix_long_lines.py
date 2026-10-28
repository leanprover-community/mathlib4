#!/usr/bin/env python3
"""Break too-long lines at the last comma before column 100.

Usage: scripts/fix_long_lines.py <path>:<line> ...

For each specified (path, line) pair, if that line exceeds 100 chars,
find the last comma before column 100 and break there, indenting the
continuation with the original indent + 2 spaces. If that doesn't bring
the line under 100, keep cutting at earlier commas.
"""
import sys
from pathlib import Path


def fix_line(text: str, lineno: int) -> str:
    lines = text.splitlines(keepends=True)
    if lineno - 1 >= len(lines):
        return text
    line = lines[lineno - 1].rstrip("\n")
    if len(line) <= 100:
        return text
    indent = len(line) - len(line.lstrip())
    leading = line[:indent]
    # Find last comma at or before col 99 (0-indexed 98)
    cut = line.rfind(",", 0, 100)
    if cut == -1:
        return text
    head = line[: cut + 1]
    tail = line[cut + 1 :].lstrip()
    new_line = head + "\n" + leading + "  " + tail + "\n"
    lines[lineno - 1] = new_line
    return "".join(lines)


def main() -> int:
    seen = set()
    by_file: dict[str, list[int]] = {}
    for a in sys.argv[1:]:
        if ":" not in a:
            continue
        path, ln = a.rsplit(":", 1)
        by_file.setdefault(path, []).append(int(ln))

    total_fixed = 0
    for path, lns in by_file.items():
        p = Path(path)
        if not p.exists():
            print(f"  skip (missing): {path}", file=sys.stderr)
            continue
        text = p.read_text()
        # Process in reverse order so line numbers stay valid after insertion
        for ln in sorted(set(lns), reverse=True):
            new = fix_line(text, ln)
            if new != text:
                text = new
                total_fixed += 1
        p.write_text(text)
    print(f"Fixed {total_fixed} long lines", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
