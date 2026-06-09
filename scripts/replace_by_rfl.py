#!/usr/bin/env python3
"""
Replace ':= by rfl' (single-line) and ':= by\\n  rfl' (two-line) with ':= rfl'
in Lean files where it is safe to do so.

Algorithm:
  1. Apply all replacements
  2. Build changed modules with lake
  3. If a file has ANY build error, revert it entirely
  4. Repeat from 2 until clean

Run from the repo root:
  python3 scripts/replace_by_rfl.py

To resume after an interrupted run:
  python3 scripts/replace_by_rfl.py --no-apply

Lake build output per iteration: /tmp/lake_build_<n>.log
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXCLUDED_DIRS = {'MathlibTest', '.lake'}
ERROR_RE = re.compile(r'^error: (.+?\.lean):(\d+):\d+:', re.MULTILINE)


def lean_module(path: Path) -> str:
    return str(path.relative_to(ROOT)).removesuffix('.lean').replace('/', '.')


def should_include(path: Path) -> bool:
    return not any(part in EXCLUDED_DIRS for part in path.parts)


def replace_in_text(text: str) -> tuple[str, int]:
    """Apply replacements; return (new_text, count)."""
    lines = text.splitlines(keepends=True)
    result = []
    count = 0
    i = 0
    while i < len(lines):
        line = lines[i]
        core = line.rstrip('\n\r')
        # Two-line: ends with ':= by' and next line is '  rfl' (exactly 2 spaces)
        if (core.rstrip().endswith(':= by')
                and i + 1 < len(lines)
                and lines[i + 1].rstrip('\n\r') == '  rfl'):
            ending = '\n' if line.endswith('\n') else ''
            result.append(core.rstrip()[:-len('by')] + 'rfl' + ending)
            count += 1
            i += 2  # consume the 'rfl' line
        # Single-line: ':= by rfl'
        elif ':= by rfl' in line:
            result.append(line.replace(':= by rfl', ':= rfl'))
            count += 1
            i += 1
        else:
            result.append(line)
            i += 1
    return ''.join(result), count


def apply_all_changes() -> tuple[dict[Path, str], int]:
    """Apply replacements. Returns ({file: original_text}, total_count)."""
    changed: dict[Path, str] = {}
    total = 0
    for lean_file in sorted(ROOT.glob('**/*.lean')):
        if not should_include(lean_file):
            continue
        text = lean_file.read_text()
        new_text, n = replace_in_text(text)
        if n > 0:
            changed[lean_file] = text
            lean_file.write_text(new_text)
            total += n
    return changed, total


def load_changes_from_git_diff() -> dict[Path, str]:
    """Reconstruct {file: original_text} from current git diff (--no-apply mode)."""
    result = subprocess.run(
        ['git', 'diff', '--name-only', 'HEAD'],
        cwd=ROOT, capture_output=True, text=True, check=True,
    )
    changed: dict[Path, str] = {}
    for rel_path in result.stdout.splitlines():
        full_path = ROOT / rel_path
        if full_path.suffix != '.lean' or not should_include(full_path):
            continue
        orig = subprocess.run(
            ['git', 'show', f'HEAD:{rel_path}'],
            cwd=ROOT, capture_output=True, text=True, check=True,
        ).stdout
        changed[full_path] = orig
    return changed


def build(modules: list[str], iteration: int) -> tuple[int, str]:
    log_path = Path(f'/tmp/lake_build_{iteration}.log')
    print(f'  (lake output → {log_path})', flush=True)
    collected: list[str] = []
    with open(log_path, 'w') as log:
        proc = subprocess.Popen(
            ['lake', 'build'] + modules,
            cwd=ROOT,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        for line in proc.stdout:
            print(line, end='', flush=True)
            log.write(line)
            collected.append(line)
        proc.wait()
    return proc.returncode, ''.join(collected)


def parse_error_files(output: str) -> set[Path]:
    files: set[Path] = set()
    for m in ERROR_RE.finditer(output):
        p = Path(m.group(1))
        if not p.is_absolute():
            p = ROOT / p
        files.add(p.resolve())
    return files


def revert_broken_files(changed: dict[Path, str], error_files: set[Path]) -> int:
    """Revert entire files that have any build error. Returns count reverted."""
    reverted = 0
    for lean_file in list(changed.keys()):
        if lean_file.resolve() in error_files:
            lean_file.write_text(changed.pop(lean_file))
            reverted += 1
    return reverted


def run_loop(changed: dict[Path, str]) -> None:
    total_files = len(changed)
    iteration = 0
    total_reverted = 0

    while True:
        iteration += 1
        modules = [lean_module(f) for f in changed]
        if not modules:
            print('All remaining changes passed — build is clean.')
            break

        print(f'Iteration {iteration}: building {len(modules)} module(s)...', flush=True)
        rc, output = build(modules, iteration)

        if rc == 0:
            print('Build succeeded!')
            break

        error_files = parse_error_files(output)
        print(f'  Errors in {len(error_files)} file(s).', flush=True)

        reverted = revert_broken_files(changed, error_files)
        total_reverted += reverted
        print(f'  Reverted {reverted} file(s).', flush=True)

        if reverted == 0:
            print('\nERROR: Build failed but no changed files matched error locations.')
            print('Failing files:')
            for f in sorted(error_files):
                try:
                    print(f'  {f.relative_to(ROOT)}')
                except ValueError:
                    print(f'  {f}')
            print('\nBuild output tail:')
            print('\n'.join(output.splitlines()[-40:]))
            sys.exit(1)

    kept = len(changed)
    print(f'\nDone. {kept}/{total_files} files kept ({total_reverted} reverted).')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--no-apply', action='store_true',
                        help='Skip applying changes; reconstruct state from git diff')
    args = parser.parse_args()

    if args.no_apply:
        print('Reconstructing applied changes from git diff...')
        changed = load_changes_from_git_diff()
        print(f'Found {len(changed)} previously-modified files.\n')
    else:
        print('Applying := by rfl / := by\\n  rfl  →  := rfl changes...')
        changed, total = apply_all_changes()
        print(f'Applied {total} change(s) in {len(changed)} file(s).\n')

    if not changed:
        print('Nothing to do.')
        return

    run_loop(changed)


if __name__ == '__main__':
    main()
