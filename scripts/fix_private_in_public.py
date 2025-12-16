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


TARGET_LINE = "@[expose] public section"
INSERT = ["", "set_option backward.privateInPublic false", "set_option backward.privateInPublic.warn true"]


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
            next_chunk = "\n".join(lines[j : min(n, j + 6)])
            if "set_option backward.privateInPublic" in next_chunk:
                # already present for this occurrence
                pass
            else:
                out.extend(INSERT)
                changed = True
        i += 1

    new_text = "\n".join(out) + ("\n" if text.endswith("\n") else "")
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
    ap.add_argument("--git-commit", action="store_true", help="Commit changes (requires --apply)")
    args = ap.parse_args()

    list_path = Path(args.list)
    files = get_files_from_list(list_path)
    if not files:
        print("No .lean files found in the list.")
        return 0

    changed_files: list[Path] = []
    for f in files:
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
