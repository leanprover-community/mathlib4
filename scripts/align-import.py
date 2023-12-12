#!/usr/bin/env python3

# This script was written by ChatGPT.
# https://chat.openai.com/share/e0363ebf-ed6f-4fd8-9b76-ebf422ed9f62

import re
import sys

def update_file_header(file_path):
    with open(file_path, 'r') as f:
        lines = f.readlines()

    # Initialize variables
    end_of_header_index = 0
    source_module = ""
    repo_ref = ""
    commit_id = ""

    # Lines to delete
    delete_indices = []

    for i, line in enumerate(lines):
        # Check for the end of the "import" lines
        if line.startswith('import'):
            end_of_header_index = i
        elif end_of_header_index != 0 and not line.startswith('import'):
            break

        # Extract the necessary info for the align import line and mark lines for deletion
        if line.startswith('! This file was ported from'):
            source_module = line.split()[-1]
            delete_indices.append(i)
        elif line.startswith('!') and 'commit' in line and commit_id == "":
            split_line = line.split()
            repo_ref = split_line[1]
            commit_id = split_line[-1]
            delete_indices.append(i)
        elif line.startswith('!'):
            delete_indices.append(i)
        elif line == "\n" and lines[i+1].startswith("!"):
            delete_indices.append(i)

    # Only proceed if we have found the necessary info for the align import line
    if source_module and repo_ref and commit_id:
        # Generate the new line
        new_line = f'\n#align_import {source_module} from "{repo_ref}"@"{commit_id}"\n'

        # Delete the marked lines
        for index in sorted(delete_indices, reverse=True):
            del lines[index]

        # Insert the new line after the "import" lines
        lines.insert(end_of_header_index - len(delete_indices) + 1, new_line)

        # Write the updated lines back to the file
        with open(file_path, 'w') as f:
            f.writelines(lines)

# The first command line argument is the file path
file_path = sys.argv[1]
update_file_header(file_path)
