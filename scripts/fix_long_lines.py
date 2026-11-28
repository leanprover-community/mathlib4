#!/usr/bin/env python3
"""Break too-long lines at the last comma before column 100.

Usage: scripts/fix_long_lines.py <path>:<line> ...

For each specified (path, line) pair, if that line exceeds 100 chars,
break at the last code comma before column 100, indenting the continuation
with the original indent + 2 spaces. Leave the line alone if the scanner
cannot identify a suitable comma.
"""
import re
import sys
from pathlib import Path


# Only recognize the spans that may contain a literal comma. Inside a block
# comment only its nesting delimiters matter, even when the text contains quotes.
BLOCK_DELIMITER = re.compile(r"/-|-/")

CODE_DELIMITER = re.compile(r"""
    --[^\n]* | /- | ,
  | «[^»]*(?:»|\Z)
  | (?<![\w'!?»]) '(?:\\.|[^'\\])'
  | (?<![\w'!?.»]) r(?P<hashes>\#*)" .*? (?:"(?P=hashes)|\Z)
  | " (?: [^"\\{] | \\. | \{[\w\s.]*\} )* (?: " | (?P<complex_hole>\{) | \Z )
""", re.VERBOSE | re.DOTALL)


def last_code_comma(text: str, start: int, end: int) -> int:
    """Return the column of the last code comma in [start, end), or -1."""
    pos = 0
    comment_depth = 0
    cut = -1
    while pos < end:
        match = (BLOCK_DELIMITER if comment_depth else CODE_DELIMITER).search(text, pos)
        if match is None or match.start() >= end:
            break
        pos = match.end()
        token = match[0]
        if token == "/-":
            comment_depth += 1
        elif token == "-/":
            comment_depth -= 1
        elif token == "," and match.start() >= start:
            cut = match.start() - start
        elif match.lastgroup == "complex_hole":
            # Interpolants can contain arbitrary Lean terms with nested strings.
            # Once the quote boundary is uncertain, leave later commas alone.
            break
    return cut


def fix_line(text: str, lineno: int) -> str:
    lines = text.splitlines(keepends=True)
    if lineno - 1 >= len(lines):
        return text
    line = lines[lineno - 1].rstrip("\n")
    if len(line) <= 100:
        return text
    indent = len(line) - len(line.lstrip())
    leading = line[:indent]
    start = sum(len(previous) for previous in lines[:lineno - 1])
    cut = last_code_comma(text, start, start + 100)
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
