#!/usr/bin/env python3
"""Remove unused-simp-argument warnings from Mathlib.

Usage: lake build 2>&1 | scripts/fix_unused_simp_args.py
   or: scripts/fix_unused_simp_args.py <build-log>

Parses warnings of the form
    warning: path:line:col: This simp argument is unused:
      <arg-name>
and rewrites the simp call at path:line to drop <arg-name>
from its argument list.
"""
from __future__ import annotations

import re
import sys
from collections import defaultdict
from pathlib import Path

WARNING_RE = re.compile(
    r"^warning: (?P<path>[^:]+\.lean):(?P<line>\d+):(?P<col>\d+): "
    r"This simp argument is unused:\s*$"
)


def parse_log(lines: list[str]) -> list[dict]:
    """Return list of {'path','line','col','arg'} dicts."""
    warnings = []
    i = 0
    while i < len(lines):
        m = WARNING_RE.match(lines[i])
        if m:
            # Next non-blank line is the arg name (indented).
            j = i + 1
            while j < len(lines) and lines[j].strip() == "":
                j += 1
            if j < len(lines):
                arg = lines[j].strip()
                warnings.append(
                    {
                        "path": m["path"],
                        "line": int(m["line"]),
                        "col": int(m["col"]),
                        "arg": arg,
                    }
                )
            i = j + 1
        else:
            i += 1
    return warnings


def find_simp_call(
    text: str, warn_line: int, warn_col: int
) -> tuple[int, int] | None:
    """Find the `[...]` span of the simp call at warn_line:warn_col (1-indexed).

    Returns (start_offset, end_offset) both inclusive of the brackets,
    or None if not found.
    """
    # Convert line:col (1-indexed) to absolute offset
    lines = text.splitlines(keepends=True)
    if warn_line - 1 >= len(lines):
        return None
    offset = sum(len(x) for x in lines[: warn_line - 1]) + warn_col

    # Walk forward from warn_col-ish to find `[`.
    # Scan backward to start of `simp` call though — warn_col points at arg,
    # so we walk back to find the opening `[`.
    i = offset
    depth = 0
    while i >= 0 and i < len(text):
        ch = text[i]
        if ch == "]":
            depth += 1
        elif ch == "[":
            if depth == 0:
                start = i
                break
            depth -= 1
        i -= 1
    else:
        return None

    # Walk forward from start to find matching `]`
    depth = 0
    i = start
    while i < len(text):
        ch = text[i]
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth -= 1
            if depth == 0:
                return (start, i)
        i += 1
    return None


def split_top_level(args_text: str) -> list[tuple[int, int]]:
    """Split a bracket-body into (start, end) offsets of comma-separated items.

    Offsets are relative to args_text. Respects nested brackets.
    """
    items = []
    depth = 0
    start = 0
    for i, ch in enumerate(args_text):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == "," and depth == 0:
            items.append((start, i))
            start = i + 1
    items.append((start, len(args_text)))
    return items


def _bare_name(s: str) -> tuple[str, str]:
    """Strip leading `←`/`-` (and whitespace) from a simp arg.

    Returns (prefix, bare_name) where prefix is one of '', '←', '-'.
    """
    stripped = s.strip()
    m = re.match(r"^(←|-)\s*(.*)$", stripped)
    if m:
        return m.group(1), m.group(2).strip()
    return "", stripped


def arg_matches(item_text: str, target_arg: str) -> bool:
    _, item_bare = _bare_name(item_text)
    _, target_bare = _bare_name(target_arg)
    return item_bare == target_bare


def remove_arg(
    text: str, span: tuple[int, int], target_arg: str
) -> tuple[str, bool]:
    """Remove (or `-`-ify) the first occurrence of target_arg in the span.

    If the item starts with `←`, rewrite it to `-` instead of removing
    (simp's own hint says the `←` is load-bearing for simp-set manipulation
    even when the rewrite itself is unused).

    Returns (new_text, success).
    """
    lb, rb = span
    inner = text[lb + 1 : rb]
    items = split_top_level(inner)
    for idx, (a, b) in enumerate(items):
        item_text = inner[a:b]
        if not arg_matches(item_text, target_arg):
            continue
        prefix, bare = _bare_name(item_text)
        if prefix == "←":
            # Replace `← X` with `- X` (keep leading whitespace).
            leading_ws = item_text[: len(item_text) - len(item_text.lstrip())]
            replacement = f"{leading_ws}- {bare}"
            new_inner = inner[:a] + replacement + inner[b:]
            return text[: lb + 1] + new_inner + text[rb:], True
        # Plain removal: also take out a comma separator
        if idx < len(items) - 1:
            remove_start = a
            remove_end = items[idx + 1][0]
        elif idx > 0:
            prev_end = items[idx - 1][1]
            remove_start = prev_end
            remove_end = b
        else:
            remove_start = a
            remove_end = b
        new_inner = inner[:remove_start] + inner[remove_end:]
        return text[: lb + 1] + new_inner + text[rb:], True
    return text, False


def main() -> int:
    if len(sys.argv) > 1:
        with open(sys.argv[1]) as f:
            lines = f.read().splitlines()
    else:
        lines = sys.stdin.read().splitlines()

    warnings = parse_log(lines)
    print(f"Parsed {len(warnings)} unused-simp-arg warnings", file=sys.stderr)

    # Group by file
    by_file: dict[str, list[dict]] = defaultdict(list)
    for w in warnings:
        by_file[w["path"]].append(w)

    total_fixed = 0
    total_failed = 0
    for path, ws in by_file.items():
        p = Path(path)
        if not p.exists():
            print(f"  skip (missing): {path}", file=sys.stderr)
            continue
        text = p.read_text()
        # Process warnings in reverse order so earlier offsets stay valid
        ws_sorted = sorted(
            ws, key=lambda w: (w["line"], w["col"]), reverse=True
        )
        file_fixed = 0
        file_failed = 0
        for w in ws_sorted:
            span = find_simp_call(text, w["line"], w["col"])
            if span is None:
                file_failed += 1
                continue
            new_text, ok = remove_arg(text, span, w["arg"])
            if ok:
                text = new_text
                file_fixed += 1
            else:
                file_failed += 1
        if file_fixed > 0:
            p.write_text(text)
            print(f"  {path}: fixed {file_fixed}"
                  + (f", failed {file_failed}" if file_failed else ""))
        else:
            print(f"  {path}: all {file_failed} failed")
        total_fixed += file_fixed
        total_failed += file_failed

    print(
        f"\nTotal: fixed {total_fixed}, failed {total_failed}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
