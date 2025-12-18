#!/usr/bin/env python3
"""
Fix occurrences of the exact line:

    @[expose] public section

by inserting the following lines immediately after it (with a blank line between):

    set_option backward.privateInPublic false
    set_option backward.privateInPublic.warn true

The script reads a file list (default: `warnings_only.txt`) and processes each
`.lean` file listed there. By default it runs as a dry-run and prints unified
diffs for each file that would change. Use `--apply` to write changes in-place
and `--git-commit` (with `--apply`) to commit them.
"""

from __future__ import annotations
import argparse
import difflib
from pathlib import Path
import sys
import subprocess
import re


TARGET_LINE = "@[expose] public section"
INSERT = ["", "set_option backward.privateInPublic false", "set_option backward.privateInPublic.warn true"]
SET1 = "set_option backward.privateInPublic false"
SET2 = "set_option backward.privateInPublic.warn true"


def process_file(path: Path) -> tuple[bool, str]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    out: list[str] = []
    changed = False
    i = 0
    n = len(lines)
    while i < n:
        out.append(lines[i])
        if lines[i].strip() == TARGET_LINE:
            # Examine the next few lines to see if we've already got the option
            j = i + 1
            # capture up to the next 6 lines (should be enough)
            next_chunk_lines = lines[j : min(n, j + 6)]
            next_chunk = "\n".join(next_chunk_lines)
            if "set_option backward.privateInPublic" in next_chunk:
                # already present for this occurrence -> leave as-is
                pass
            else:
                out.extend(INSERT)
                changed = True
        i += 1

    new_text = "\n".join(out) + ("\n" if text.endswith("\n") else "")
    return changed, new_text


def revert_file(path: Path) -> tuple[bool, str]:
    """Remove previously-inserted set_option lines after the target line."""
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    out: list[str] = []
    changed = False
    i = 0
    n = len(lines)
    while i < n:
        out.append(lines[i])
        if lines[i].strip() == TARGET_LINE:
            # Look ahead for the exact pattern we inserted: optional blank, then SET1 and SET2
            j = i + 1
            if j < n and lines[j].strip() == "":
                # blank present
                if j + 2 < n and lines[j + 1].strip() == SET1 and lines[j + 2].strip() == SET2:
                    # skip the blank and the two set_option lines
                    i = j + 2
                    changed = True
            else:
                # no blank; check for SET1 then SET2
                if j + 1 < n and lines[j].strip() == SET1 and lines[j + 1].strip() == SET2:
                    i = j + 1
                    changed = True
        i += 1

    new_text = "\n".join(out) + ("\n" if text.endswith("\n") else "")
    return changed, new_text


def remove_exact_file(path: Path) -> tuple[bool, str]:
    """Remove only the exact inserted block (optional blank then SET1 and SET2)
    immediately following `TARGET_LINE`.
    This uses a precise regex so it does not touch other `set_option` usages
    like `set_option ... true in`.
    """
    text = path.read_text(encoding="utf-8")
    # Capture the target line + its newline in group 1, optionally one blank line,
    # then the exact two set_option lines (allowing surrounding whitespace).
    pattern = re.compile(
        r"(^\s*@\[expose\]\s*public\s+section\s*\n)"  # group 1: target line
        r"(?:\n)?\s*"  # optional single blank line
        r"set_option\s+backward\.privateInPublic\s+false\s*\n"
        r"\s*set_option\s+backward\.privateInPublic\.warn\s+true\s*\n?",
        re.MULTILINE,
    )
    new_text, nsub = pattern.subn(r"\1", text)
    changed = nsub > 0
    return changed, new_text


def get_files_from_list(list_path: Path) -> list[Path]:
    if not list_path.exists():
        print(f"List file not found: {list_path}", file=sys.stderr)
        sys.exit(2)
    files: list[Path] = []
    import re
    for line in list_path.read_text(encoding="utf-8").splitlines():
        s = line.strip()
        if not s:
            continue
        # If the line is a plain path (ends with .lean), use it directly
        if s.endswith('.lean'):
            candidate_paths = [s]
        else:
            # Try to extract a .lean path from a warning line like:
            # warning: Mathlib/Path/To/File.lean:LINE:COL: ...
            m = re.search(r'([^\s:]+\.lean)', s)
            if m:
                candidate_paths = [m.group(1)]
            else:
                continue

        for cs in candidate_paths:
            p = Path(cs)
            if p.exists():
                files.append(p)
            else:
                candidate = list_path.parent / cs
                if candidate.exists():
                    files.append(candidate)
                else:
                    print(f"Warning: listed file not found: {cs}")
    # dedupe
    seen = set()
    out: list[Path] = []
    for p in files:
        key = str(p)
        if key not in seen:
            seen.add(key)
            out.append(p)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--list", default="warnings_only.txt", help="Path to list file")
    ap.add_argument("--apply", action="store_true", help="Apply changes in-place")
    ap.add_argument("--revert", action="store_true", help="Remove previously inserted set_option lines")
    ap.add_argument(
        "--remove-exact",
        action="store_true",
        help="Remove only the exact inserted set_option block after the target line",
    )
    ap.add_argument("--git-commit", action="store_true", help="Commit changes (requires --apply)")
    args = ap.parse_args()

    list_path = Path(args.list)
    files = get_files_from_list(list_path)
    if not files:
        print("No .lean files found in the list.")
        return 0

    changed_files: list[Path] = []
    # Ensure flags are used sensibly
    if args.revert and args.remove_exact:
        print("Error: --revert and --remove-exact are mutually exclusive", file=sys.stderr)
        return 2

    for f in files:
        if args.remove_exact:
            changed, new_text = remove_exact_file(f)
        elif args.revert:
            changed, new_text = revert_file(f)
        else:
            changed, new_text = process_file(f)
        if changed:
            old_text = f.read_text(encoding="utf-8")
            diff = difflib.unified_diff(
                old_text.splitlines(keepends=True),
                new_text.splitlines(keepends=True),
                fromfile=str(f),
                tofile=str(f) + " (modified)",
            )
            sys.stdout.writelines(diff)
            changed_files.append(f)
            if args.apply:
                bak = f.with_suffix(f.suffix + ".bak")
                bak.write_text(old_text, encoding="utf-8")
                f.write_text(new_text, encoding="utf-8")

    if changed_files:
        print(f"\nTotal files changed: {len(changed_files)}")
        for p in changed_files:
            print(f" - {p}")
        if args.apply and args.git_commit:
            try:
                subprocess.run(["git", "add"] + [str(p) for p in changed_files], check=True)
                if args.revert:
                    msg = "Remove backward.privateInPublic set_option after @[expose] public section"
                elif args.remove_exact:
                    msg = "Remove exact backward.privateInPublic set_option block after @[expose] public section"
                else:
                    msg = "Insert backward.privateInPublic set_option after @[expose] public section"
                subprocess.run(["git", "commit", "-m", msg], check=True)
                print("Committed the changes.")
            except subprocess.CalledProcessError as e:
                print("Git commit failed:", e, file=sys.stderr)
                return 1
    else:
        print("No files needed changes.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
