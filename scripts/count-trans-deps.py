#!/usr/bin/env python3

# Reports the number of transitive import dependencies
# of each file in a directory of a Lean project.
# The directory name is provided as a command line argument.
# The number of transitive import dependencies is printed to the console as JSON dictionary.

import os
import re
import json
import sys

def get_imports(directory):
    # Initialize an empty dictionary
    file_imports = {}

    # Iterate over all Lean files in the given directory
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith('.lean'):
                # Full path to the file
                file_path = os.path.join(root, file)

                # Normalize the filename
                module_name = file_path.replace('/', '.').replace('.lean', '')

                # Open the file and read it line by line
                imports = []
                with open(file_path, 'r') as f:
                    for line in f:
                        # Stop reading the file if the line contains `/-!`
                        if '/-!' in line:
                            break
                        # Find an import statement
                        match = re.match(r'^import\s+(.*)', line)
                        if match:
                            imports.append(match.group(1))

                # Add the file and its imports to the dictionary
                file_imports[module_name] = imports

    return file_imports

def get_transitive_imports(file_imports):
    # Initialize a dictionary to store the transitive imports
    transitive_imports = {}
    # Initialize a set to store the visited files
    visited = set()

    def dfs(file):
        if file not in visited:
            visited.add(file)
            if file in file_imports:
                transitive_imports[file] = set(file_imports[file])
                for import_module in file_imports[file]:
                    if import_module in file_imports:
                        transitive_imports[file].update(dfs(import_module))
            else:
                transitive_imports[file] = set()
        return transitive_imports[file]

    # Compute the transitive imports for each file
    for file in file_imports:
        dfs(file)

    return transitive_imports

def count_transitive_imports(transitive_imports):
    # Initialize a dictionary to store the counts
    count_imports = {}

    # Iterate over the dictionary of transitive imports
    for file, imports in transitive_imports.items():
        # The count is the size of the set of transitive imports
        count_imports[file] = len(imports)

    return count_imports

# Check if the directory name is provided as a command line argument
if len(sys.argv) < 2:
    print("Please provide the directory name as a command line argument.")
    sys.exit(1)

# Get the directory name from the command line argument
directory = sys.argv[1]

# Compute the counts
counts = count_transitive_imports(get_transitive_imports(get_imports(directory)))

# Print the counts in JSON format
print(json.dumps(counts))
