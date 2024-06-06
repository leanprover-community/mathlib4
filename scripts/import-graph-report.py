#! /usr/bin/env python3

# This script compares the counts of dependencies between two JSON files.
# It takes two file paths as command line arguments,
# loads the counts from each file, and then compares the counts.
# It identifies dependencies that have either decreased or increased,
# and generates a message with a summary of the changes.
# The message is printed to the console.

import json
import sys

def compare_counts(base_file, head_file):
    # Load the counts
    with open(head_file, 'r') as f:
        head_counts = json.load(f)
    with open(base_file, 'r') as f:
        base_counts = json.load(f)

    # Compute the number of new files
    new_files = len(set(head_counts.keys()) - set(base_counts.keys()))

    # Compare the counts
    changes = []
    for file, head_count in head_counts.items():
        base_count = base_counts.get(file, 0)
        if base_count > 0 and head_count < base_count:  # Dependencies went down
            diff = base_count - head_count
            percent = (diff / base_count) * 100
            changes.append((file, base_count, head_count, -diff, -percent))
        elif head_count > base_count + new_files:  # Dependencies went up by more than the number of new files
            diff = head_count - base_count
            percent = (diff / base_count) * 100 if base_count > 0 else 100
            changes.append((file, base_count, head_count, diff, percent))

    # Sort the changes by the absolute value of the percentage change
    changes.sort(key=lambda x: abs(x[4]), reverse=True)

    # Build the messages
    messages = []
    for file, base_count, head_count, diff, percent in changes:
        sign = "+" if diff > 0 else "-"
        messages.append(f'| {file} | {base_count} | {head_count} | {sign}{abs(diff)} ({sign}{abs(percent):.2f}%) |')

    # Build the message
    message = '### Import summary\n\n<details><summary>Dependency changes</summary>\n\n'
    if messages:
        message += '| File | Base Count | Head Count | Change |\n'
        message += '| --- | --- | --- | --- |\n'
        message += '\n'.join(messages)
    else:
        message += 'None'
    message += '\n</details>'
    return message

if __name__ == '__main__':
    base_file = sys.argv[1]
    head_file = sys.argv[2]
    message = compare_counts(base_file, head_file)
    print(message)
