#!/usr/bin/env python3

import os
import re
from collections import defaultdict
import textwrap

# Path to the Mathlib directory
MATHLIB_PATH = "Mathlib"

def get_top_level_directories(path):
    """Enumerate top-level subdirectories in the given path."""
    return [
        name for name in os.listdir(path)
        if os.path.isdir(os.path.join(path, name)) and not name.startswith(".")
    ]

def find_import_statements(file_path):
    """Extract `import Mathlib.X.Y.Z` statements from a file."""
    import_statements = []
    with open(file_path, "r", encoding="utf-8") as file:
        for line in file:
            match = re.match(r"^import Mathlib\.([\w\.]+)", line.strip())
            if match:
                import_statements.append(match.group(1))
    return import_statements

def analyze_imports(mathlib_path, top_level_dirs):
    """Analyze import statements across all `.lean` files."""
    import_counts = defaultdict(lambda: defaultdict(int))

    for top_dir in top_level_dirs:
        dir_path = os.path.join(mathlib_path, top_dir)
        for root, _, files in os.walk(dir_path):
            for file in files:
                if file.endswith(".lean"):
                    file_path = os.path.join(root, file)
                    imports = find_import_statements(file_path)
                    for imp in imports:
                        imported_top_dir = imp.split(".")[0]
                        if imported_top_dir in top_level_dirs and imported_top_dir != top_dir:
                            import_counts[top_dir][imported_top_dir] += 1
    return import_counts

def compute_column_sums(import_counts, top_level_dirs):
    """Compute column sums for sorting."""
    column_sums = {dir_name: 0 for dir_name in top_level_dirs}
    for source_dir in top_level_dirs:
        for target_dir in top_level_dirs:
            column_sums[target_dir] += import_counts[source_dir].get(target_dir, 0)
    return column_sums

def print_import_table(import_counts, sorted_dirs, column_sums):
    """Print a table showing the import counts."""
    # Filter out columns with a sum of 0
    filtered_dirs = [dir_name for dir_name in sorted_dirs if column_sums[dir_name] > 0]

    print(f"{'Top Level Directory':<20}", end="")
    for dir_name in filtered_dirs:
        print(f"{textwrap.shorten(dir_name, width=12, placeholder=''):<15}", end="")
    print()

    for source_dir in sorted_dirs:
        print(f"{textwrap.shorten(source_dir, width=12, placeholder=''):<20}", end="")
        for target_dir in filtered_dirs:
            count = import_counts[source_dir].get(target_dir, 0)
            if 0 < count < 5:
                print(f"\033[93m{count:<15}\033[0m", end="")  # Highlight in yellow
            else:
                print(f"{count:<15}", end="")
        print()

def main():
    top_level_dirs = get_top_level_directories(MATHLIB_PATH)
    import_counts = analyze_imports(MATHLIB_PATH, top_level_dirs)

    column_sums = compute_column_sums(import_counts, top_level_dirs)
    sorted_dirs = sorted(top_level_dirs, key=lambda d: column_sums[d], reverse=True)

    print_import_table(import_counts, sorted_dirs, column_sums)

if __name__ == "__main__":
    main()
