#!/usr/bin/env python3
"""
Automatically fixes deprecation warnings in Mathlib.

Runs `lake build --no-build` to collect warnings, then for each warning:
- Goes to the exact file:line:column position
- Tries to match the deprecated name (handling both qualified and unqualified names)
- Replaces it with the suggested replacement
"""

import subprocess
import re
from collections import defaultdict
from pathlib import Path

def main() -> None:
    # Run lake build --no-build ONCE to collect warnings without building
    print("Running lake build --no-build to collect deprecation warnings...")
    result = subprocess.run(['lake', 'build', '--no-build'], capture_output=True, text=True)
    output = result.stdout + result.stderr

    # Parse warnings
    warnings_by_file = defaultdict(list)
    skipped_files = set()

    for line in output.split('\n'):
        if 'warning:' in line and 'deprecated' in line:
            match = re.search(r'([^:]+\.lean):(\d+):(\d+):', line)
            if match:
                filepath = match.group(1).strip()  # Strip leading/trailing whitespace
                line_num = int(match.group(2))
                col_num = int(match.group(3))

                # Skip if file doesn't exist locally
                if not Path(filepath).exists():
                    if filepath not in skipped_files:
                        skipped_files.add(filepath)
                    continue

                old_match = re.search(r'`([^`]+)` has been deprecated', line)
                new_match = re.search(r'Use `([^`]+)` instead', line)

                if old_match and new_match:
                    old_name = old_match.group(1)
                    new_name = new_match.group(1)
                    warnings_by_file[filepath].append({
                        'line': line_num,
                        'col': col_num,
                        'old': old_name,
                        'new': new_name,
                    })

    total_warnings = sum(len(w) for w in warnings_by_file.values())
    print(f"Found {total_warnings} warnings in {len(warnings_by_file)} files")
    if skipped_files:
        print(f"Skipped {len(skipped_files)} files not in current repository: {', '.join(sorted(skipped_files))}")
    print()

    files_changed = total_changes = 0
    skipped = []

    for filepath, warnings in sorted(warnings_by_file.items()):
        print(filepath)

        with open(filepath, 'r') as f:
            lines = f.readlines()

        # Sort by position (reverse order to avoid offset issues)
        warnings.sort(key=lambda w: (w['line'], w['col']), reverse=True)

        made_changes = False

        for warning in warnings:
            line_num = warning['line'] - 1  # Lean uses 1-indexed lines
            col_num = warning['col']        # Lean uses 0-indexed columns
            old_name = warning['old']
            new_name = warning['new']

            if line_num >= len(lines):
                print(f"  ⚠ Line {line_num + 1}, col {col_num}: Out of range")
                skipped.append((filepath, line_num + 1, col_num, old_name, "out of range"))
                continue

            line = lines[line_num]

            # Try progressively shorter versions by removing namespace prefixes.
            # E.g., for "Fin.lt_iff_val_lt_val", try "Fin.lt_iff_val_lt_val", then "lt_iff_val_lt_val".
            old_parts = old_name.split('.')
            new_parts = new_name.split('.')

            replaced = False
            for i in range(len(old_parts)):
                old_suffix = '.'.join(old_parts[i:])
                new_suffix = '.'.join(new_parts[i:]) if i < len(new_parts) else new_name

                if line[col_num:col_num+len(old_suffix)] == old_suffix:
                    lines[line_num] = line[:col_num] + new_suffix + line[col_num+len(old_suffix):]
                    print(f"  Line {line_num + 1}, col {col_num}: {old_suffix} → {new_suffix}")
                    made_changes = True
                    total_changes += 1
                    replaced = True
                    break

            if not replaced:
                actual = line[col_num:col_num+20]
                print(f"  ⚠ Line {line_num + 1}, col {col_num}: Expected '{old_name}', found '{actual}...'")
                skipped.append((filepath, line_num + 1, col_num, old_name, actual))

        if made_changes:
            with open(filepath, 'w') as f:
                f.writelines(lines)
            files_changed += 1

        print()

    print("="*80)
    print(f"Changed {total_changes} deprecations in {files_changed} files")
    if skipped:
        print(f"Skipped {len(skipped)} warnings (could not find exact match at position)")
    print("="*80)

if __name__ == '__main__':
    main()
