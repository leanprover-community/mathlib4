#! /usr/bin/env python3

# https://chatgpt.com/share/66f4e420-66bc-8001-8349-ce3cfb4f23c3
# Usage: lake build | scripts/fix_unused.py

# Bulk processing of unused variable warnings, replacing them with `_`.

import re
import sys

# Parse warning messages and extract file paths, line, column, and variable names
def parse_warnings(warning_lines):
    pattern = r"warning: (\S+):(\d+):(\d+): unused variable `([^`]+)`"
    warnings = []

    for line in warning_lines:
        match = re.match(pattern, line)
        if match:
            file_path, line_num, col_num, var_name = match.groups()
            warnings.append({
                'file_path': file_path,
                'line_num': int(line_num),
                'col_num': int(col_num),
                'var_name': var_name
            })

    return warnings

# Find the actual column index, adjusting for multi-byte Unicode characters
def find_column_index(line, target_col):
    """Return the index in the string where the column equals target_col, ignoring visual width."""
    current_col = 0
    for idx, char in enumerate(line):
        # Move one "logical column" per character (whether wide or narrow)
        if current_col >= target_col:
            return idx
        current_col += 1
    return len(line)  # Return the end if column number exceeds the line length

# Replace variable with `_` at the specified line and column in the file
def process_file(file_path, edits):
    with open(file_path, 'r', encoding='utf-8') as f:
        lines = f.readlines()

    for edit in sorted(edits, key=lambda e: e['line_num'], reverse=True):
        line_num = edit['line_num'] - 1
        col_num = edit['col_num'] - 1
        var_name = edit['var_name']
        line = lines[line_num]

        # Find the actual starting column index for the variable
        actual_col = find_column_index(line, col_num)

        # Replace the variable with `_`
        new_line = line[:actual_col] + line[actual_col:].replace(var_name, '_', 1)
        lines[line_num] = new_line

    with open(file_path, 'w', encoding='utf-8') as f:
        f.writelines(lines)

# Process all warnings
def process_warnings(warnings):
    file_edits = {}

    # Organize warnings by file
    for warning in warnings:
        file_path = warning['file_path']
        if file_path not in file_edits:
            file_edits[file_path] = []
        file_edits[file_path].append(warning)

    # Process each file in reverse order of warnings
    for file_path, edits in file_edits.items():
        print(f"Processing {file_path} with {len(edits)} edits.")
        process_file(file_path, edits)

if __name__ == "__main__":
    # Read warning lines from stdin
    warning_lines = sys.stdin.read().splitlines()

    # Parse and process warnings
    warnings = parse_warnings(warning_lines)
    process_warnings(warnings)
