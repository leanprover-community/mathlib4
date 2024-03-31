#!/usr/bin/env python3
import os

def add_namespace_mathlib(root_directory):
    # Directories and specific .lean files to exclude
    excluded_dirs = [
        'Lean',
        'Init',
        'Util',
        'Tactic',
        'Data/String',
        'Data/Rat',
        'Data/List',
        'Data/Array',
        'Data/BitVec',
        'Data/Bool',
        'Data/Int',
        'Data/Nat',
        'Data/HashMap',
        'Data/BinaryHeap',
        'Data/MLList',
        'Data/DList',
        'Data/Option',
        'Data/Prod',
        'Data/Sum',
        'Data/Sigma',
        'Data/Subtype',
        'Data/Quot',
        'Order/Basic',
        'Control',
        'Logic',
        'Mathport',
        'Algebra/Group/Defs'
    ]

    # Generate a list of specific .lean files to exclude based on excluded_dirs
    excluded_files = [ed.replace('/', '.') + '.lean' for ed in excluded_dirs]

    # Convert to full paths for checking against the current root in the loop
    excluded_paths = [os.path.join(root_directory, ed) for ed in excluded_dirs]

    for root, dirs, files in os.walk(root_directory, topdown=True):
        # Filter out the dirs list to exclude specific paths
        dirs[:] = [d for d in dirs if os.path.join(root, d) not in excluded_paths]

        for file in files:
            file_path = os.path.join(root, file)
            # Check if the file or its directory is excluded
            if file.endswith('.lean') and not any(file_path.startswith(path) for path in excluded_paths) and file not in excluded_files:
                with open(file_path, 'r') as f:
                    lines = f.readlines()

                # Skip file if 'namespace Mathlib' or 'end Mathlib' already exists
                if any('namespace Mathlib' in line for line in lines) or any('end Mathlib' in line for line in lines):
                    continue

                for i, line in enumerate(lines):
                    if line.startswith('#align '):
                        parts = line.split(' ', 2)
                        if len(parts) == 3 and not parts[2].startswith('Mathlib.'):
                            lines[i] = f"#align {parts[1]} Mathlib.{parts[2]}"

                insert_index = find_insertion_index(lines)

                lines.insert(insert_index, '\nnamespace Mathlib\n')
                lines.append('\nend Mathlib\n')

                with open(file_path, 'w') as f:
                    f.writelines(lines)

def find_insertion_index(lines):
    insert_index, in_docstring, seen_import = 0, False, False
    for i, line in enumerate(lines):
        if line.strip().startswith('/-') and not in_docstring:
            in_docstring = True
            continue
        if '-/' in line.strip() and in_docstring:
            in_docstring = False
            continue
        if not in_docstring and (line.startswith('import ') or (line.startswith('#align_import') and seen_import)):
            insert_index = i + 1
            seen_import = True
        elif not in_docstring and seen_import and not line.strip() and not line.startswith('#align_import'):
            continue
        elif not in_docstring and seen_import and line.strip() and not line.startswith('import ') and not line.startswith('#align_import'):
            break
    return insert_index

if __name__ == '__main__':
    add_namespace_mathlib('Mathlib')
