#!/usr/bin/env python3
"""
Fix privateInPublic warnings by adding set_option statements.

This script:
1. Parses warnings to find files with private-in-public issues
2. For each warning, adds:
   - `set_option backward.privateInPublic true in` before the private declaration (callee)
   - Both set_options before the public declaration accessing it (caller)
"""

from __future__ import annotations
import re
import sys
from pathlib import Path
from collections import defaultdict
from typing import NamedTuple


class Warning(NamedTuple):
    file: str
    line: int
    col: int
    private_decl: str


def parse_warnings(warnings_file: Path) -> dict[str, list[Warning]]:
    """Parse warnings file and group by file path."""
    warnings_by_file = defaultdict(list)

    pattern = r"warning: ([^:]+):(\d+):(\d+): Private declaration ['\u2018]([^'\u2019]+)['\u2019] accessed publicly"

    for line in warnings_file.read_text().splitlines():
        match = re.match(pattern, line)
        if match:
            file_path, line_num, col, private_decl = match.groups()
            warnings_by_file[file_path].append(
                Warning(file_path, int(line_num), int(col), private_decl)
            )

    return warnings_by_file


def find_declaration_start(lines: list[str], line_idx: int) -> int:
    """
    Find the start of a declaration by searching backwards for:
    - Structure/class/def/theorem/lemma/instance keywords
    - Attribute annotations (@[...])
    - Doc comments (/-! or /-- )

    Returns the line index where we should insert set_option.
    """
    i = line_idx

    # First, find the actual declaration line (skip back from the access point)
    # Look for declaration keywords
    decl_keywords = ['structure', 'class', 'def', 'theorem', 'lemma', 'instance', 'abbrev', 'private']

    while i >= 0:
        line = lines[i].lstrip()
        # Check if this line starts a declaration
        if any(line.startswith(kw + ' ') or f' {kw} ' in line for kw in decl_keywords):
            break
        i -= 1

    if i < 0:
        return line_idx  # Fallback to original line

    decl_line = i

    # Now search backwards for attributes and doc comments
    i = decl_line - 1
    while i >= 0:
        line = lines[i].strip()

        # Skip empty lines
        if not line:
            i -= 1
            continue

        # If it's an attribute or doc comment, keep going
        if line.startswith('@[') or line.startswith('/-') or line == '-/':
            i -= 1
            continue

        # If it's a variable declaration, keep going
        if line.startswith('variable'):
            i -= 1
            continue

        # Otherwise, we've found the start
        break

    # Insert after the last non-declaration line
    return i + 1


def needs_set_option(lines: list[str], insert_line: int) -> bool:
    """Check if set_option is already present at this location."""
    # Check a few lines before and after
    for offset in range(-2, 3):
        idx = insert_line + offset
        if 0 <= idx < len(lines):
            if 'set_option backward.privateInPublic' in lines[idx]:
                return False
    return True


def add_set_options(file_path: Path, warnings: list[Warning], dry_run: bool = True) -> bool:
    """
    Add set_option statements to a file based on warnings.
    Returns True if changes were made.
    """
    lines = file_path.read_text(encoding='utf-8').splitlines()

    # Track lines where we need to add set_options (caller lines)
    caller_lines = set()
    private_decls = {}  # Maps private declaration name to its line

    # First pass: identify all warning locations
    for warning in warnings:
        # Warnings are 1-indexed, convert to 0-indexed
        line_idx = warning.line - 1
        caller_lines.add(line_idx)

    # Find private declarations by searching the file
    for i, line in enumerate(lines):
        if 'private' in line and ('::' in line or 'def ' in line or 'theorem ' in line or 'lemma ' in line):
            # Extract declaration name
            match = re.search(r'private\s+(?:nonrec\s+)?(?:theorem|lemma|def|structure|class)\s+(\w+)', line)
            if not match:
                # Try private constructor pattern
                match = re.search(r'private\s+(\w+)\s*::', line)
            if match:
                decl_name = match.group(1)
                private_decls[decl_name] = i

    # Collect all insertions (line_num, text, is_caller)
    insertions = []

    # Add set_options for callers (the warning lines)
    for line_idx in sorted(caller_lines, reverse=True):
        insert_line = find_declaration_start(lines, line_idx)
        if needs_set_option(lines, insert_line):
            insertions.append((insert_line, 'caller', warning.private_decl))

    # Add set_options for private declarations
    for decl_name, line_idx in private_decls.items():
        insert_line = find_declaration_start(lines, line_idx)
        if needs_set_option(lines, insert_line):
            insertions.append((insert_line, 'callee', decl_name))

    if not insertions:
        return False

    # Sort by line number (descending) to insert from bottom to top
    insertions.sort(reverse=True)

    # Apply insertions
    for insert_line, insertion_type, decl_name in insertions:
        if insertion_type == 'caller':
            lines.insert(insert_line, 'set_option backward.privateInPublic.warn false in')
            lines.insert(insert_line, 'set_option backward.privateInPublic true in')
        else:  # callee
            lines.insert(insert_line, 'set_option backward.privateInPublic true in')

    if dry_run:
        print(f"Would modify {file_path} with {len(insertions)} insertions")
        return True
    else:
        file_path.write_text('\n'.join(lines) + '\n', encoding='utf-8')
        print(f"Modified {file_path}")
        return True


def main():
    import argparse

    parser = argparse.ArgumentParser(description='Fix privateInPublic warnings')
    parser.add_argument('--warnings', default='warnings_only.txt', help='Warnings file')
    parser.add_argument('--apply', action='store_true', help='Apply changes (default is dry-run)')
    parser.add_argument('--files', nargs='*', help='Specific files to process')

    args = parser.parse_args()

    warnings_file = Path(args.warnings)
    if not warnings_file.exists():
        print(f"Error: {warnings_file} not found", file=sys.stderr)
        return 1

    warnings_by_file = parse_warnings(warnings_file)

    if args.files:
        # Process only specified files
        files_to_process = {f: warnings_by_file.get(f, []) for f in args.files if f in warnings_by_file}
    else:
        files_to_process = warnings_by_file

    if not files_to_process:
        print("No files to process")
        return 0

    modified_count = 0
    for file_path_str, warnings in files_to_process.items():
        file_path = Path(file_path_str)
        if not file_path.exists():
            print(f"Warning: {file_path} does not exist, skipping")
            continue

        if add_set_options(file_path, warnings, dry_run=not args.apply):
            modified_count += 1

    print(f"\n{'Modified' if args.apply else 'Would modify'} {modified_count} files")
    return 0


if __name__ == '__main__':
    sys.exit(main())
