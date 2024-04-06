#!/usr/bin/env python3
''''
Lint all files in a given directory. Use as
 $ python3 ./scripts/lint_dir.py
This avoids parsing the list of all aligns and align_imports several times.
'''

import importlib
lintstyle = importlib.import_module("lint-style")

from pathlib import Path

if __name__ == '__main__':
    # Parse the list of all files to lint, the the given directory.
    dir = 'Util'
    assert '/' not in dir
    print(f"about to lint all files in directory {dir}")
    files = []
    for line in open('Mathlib.lean', 'r', encoding='utf-8'):
        line = line[len('import Mathlib.'):].strip()
        if line.startswith(dir):
            files.append(line)
    for filename in files:
        path = f"Mathlib/{filename.replace('.', '/')}.lean"
        lintstyle.lint(Path(path), fix=False)
