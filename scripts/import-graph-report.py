#! /usr/bin/env python3

# This script compares the counts of dependencies between two JSON files.
# It takes two file paths as command line arguments,
# loads the counts from each file, and then compares the counts.
# It identifies dependencies that have either decreased or increased,
# and generates a message with a summary of the changes.
# The message is printed to the console.

import json
import sys

def compare_counts(base_file, head_file, changed_files_txt):
    # Load the counts
    with open(head_file, 'r') as f:
        head_counts = json.load(f)
    with open(base_file, 'r') as f:
        base_counts = json.load(f)

    # Load the changed files, filter for `.lean` files
    with open(changed_files_txt, 'r') as f:
        changed_files = [line.strip() for line in f if line.endswith('.lean')]

    # Replace / with . in the path, and drop the .lean extension
    changed_files = [file.replace('/', '.').replace('.lean', '') for file in changed_files]

    # Compute the number of new files
    new_files = len(set(head_counts.keys()) - set(base_counts.keys()))

    # Compare the counts
    changes = []
    for file in changed_files:
        base_count = base_counts.get(file, 0)
        if base_count > 0 and head_count < base_count:  # Dependencies went down
            diff = base_count - head_count
            percent = (diff / base_count) * 100
            changes.append((file, base_count, head_count, diff, percent))
        elif head_count > base_count + new_files:  # Dependencies went up by more than the number of new files
            diff = head_count - base_count
            percent = (diff / base_count) * 100 if base_count > 0 else 100
            changes.append((file, base_count, head_count, diff, percent))

    # Sort the changes by the absolute value of the percentage change
    changes.sort(key=lambda x: abs(x[4]), reverse=True)

    # Build the messages
    messages = []
    for file, base_count, head_count, diff, percent in changes:
        sign = "+" if diff > 0 else ""
        messages.append(f'| {file} | {base_count} | {head_count} | {sign}{diff} ({sign}{percent:.2f}%) |')

    # Build the message
    message = '### Import summary\n\n'
    if messages:
        message += '<details><summary>Dependency changes</summary>\n\n'
        message += '| File | Base Count | Head Count | Change |\n'
        message += '| --- | --- | --- | --- |\n'
        message += '\n'.join(messages)
        message += '\n</details>'
    else:
        message += 'None'
    return message

if __name__ == '__main__':
    base_file = sys.argv[1]
    head_file = sys.argv[2]
    changed_files = sys.argv[3]
    message = compare_counts(base_file, head_file, changed_files)
    print(message)
