#!/usr/bin/env python3
"""Parse the output of `lake shake` and emit summary statistics.

Reads a log produced by `lake shake` (with or without `--fix` / `--explain`)
and counts the number of files edited, the number of imports added, and
the number of imports removed. The counts are printed to stdout and, if a
second argument is given (typically `$GITHUB_OUTPUT`), appended to that
file so subsequent workflow steps can consume them.

Note: the file count is taken from the `Successfully applied N suggestions.`
line that `lake shake` only prints when run with `--fix`. Without `--fix`
the file count is reported as 0; the import counts are still accurate.

Usage: parse_shake_output.py <shake-output.txt> [$GITHUB_OUTPUT]
"""

import sys
import re
import os

def main():
    if len(sys.argv) < 2:
        print("Usage: parse_shake_output.py <shake-output.txt> [$GITHUB_OUTPUT]", file=sys.stderr)
        sys.exit(1)

    shake_output_path = sys.argv[1]
    output_path = sys.argv[2] if len(sys.argv) >= 3 else None
    if not os.path.isfile(shake_output_path):
        print(f"error: shake output file not found: {shake_output_path}", file=sys.stderr)
        sys.exit(1)
    if output_path is not None:
        output_dir = os.path.dirname(output_path) or "."
        if not os.path.isdir(output_dir):
            print(f"error: output directory does not exist: {output_dir}", file=sys.stderr)
            sys.exit(1)

    changed_files = added = removed = 0
    with open(shake_output_path) as f:
        for line in f:
            m = re.search(r'Successfully applied (\d+) suggestions', line)
            if m:
                changed_files = int(m.group(1))
            m = re.match(r'^  (add|remove) #\[(.+)\]', line)
            if m:
                action, items = m.group(1), m.group(2)
                count = len([x for x in items.split(',') if x.strip()])
                if action == 'add':
                    added += count
                else:
                    removed += count
    print(f'{changed_files} files changed · +{added} imports added · -{removed} imports removed')
    if output_path is not None:
        with open(output_path, 'a') as out:
            out.write(f'changed_files={changed_files}\n')
            out.write(f'added={added}\n')
            out.write(f'removed={removed}\n')

if __name__ == "__main__":
    main()
