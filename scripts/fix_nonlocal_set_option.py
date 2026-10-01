#!/usr/bin/env python3
"""
Fix non-local breakage from set_option removal.

For each failing module A:
1. Add the option to all dependencies of A
2. Verify A builds
3. Binary-search remove unnecessary options from deps of A,
   checking that A (and all previously-fixed modules) still build

To use outside mathlib, copy `fix_nonlocal_set_option.py`,
`add_module_set_option.py`, `rm_module_set_option.py`, `dag_traversal.py` and
`set_option_utils.py` to a subdirectory of your project named `scripts/` and
then run from the project root with `scripts/fix_nonlocal_set_option.py`.
Pass `--directories <root>` if your source files aren't directly under the
project root.

Usage:
    python3 scripts/fix_nonlocal_set_option.py MODULE1 MODULE2 ...
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

try:
    from dag_traversal import DAG
    from set_option_utils import PROJECT_DIR
    from add_module_set_option import add_to_file, find_insert_point
    from rm_module_set_option import module_set_option_pattern, scan_files
except ImportError as _e:
    raise SystemExit(
        f"error: {_e}\n\n"
        f"  This script depends on sibling Python files in {Path(__file__).parent}:\n"
        "    - dag_traversal.py\n"
        "    - set_option_utils.py\n"
        "    - add_module_set_option.py\n"
        "    - rm_module_set_option.py\n"
        "  These are mathlib scripts, not pip packages.  Copy them into your\n"
        "  `scripts/` directory alongside this script."
    )

DEFAULT_OPTION = "backward.defeq.atInstanceTransparency"


def collect_all_dependencies(dag: DAG, module_name: str) -> set[str]:
    """Collect all transitive dependencies (imports) of a module."""
    collected: set[str] = set()
    frontier = {module_name}
    while frontier:
        next_frontier: set[str] = set()
        for m in frontier:
            info = dag.modules.get(m)
            if info is None:
                continue
            for imp in info.imports:
                if imp not in collected and imp != module_name:
                    collected.add(imp)
                    next_frontier.add(imp)
        frontier = next_frontier
    return collected


def lake_build_modules(modules: list[str], timeout: int = 600) -> bool:
    """Build specific modules. Returns True if all succeed."""
    for mod in modules:
        result = subprocess.run(
            ["lake", "build", mod],
            cwd=PROJECT_DIR,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        if result.returncode != 0:
            return False
    return True


def has_option(filepath: Path, option: str, value: str) -> bool:
    """Check if a file has the module-level set_option line."""
    pat = module_set_option_pattern(option, value)
    text = filepath.read_text()
    for line in text.splitlines():
        if pat.match(line):
            return True
    return False


def remove_option(filepath: Path, option: str, value: str) -> str | None:
    """Remove the module-level set_option line. Returns original text or None."""
    pat = module_set_option_pattern(option, value)
    text = filepath.read_text()
    lines = text.splitlines(keepends=True)
    for i, line in enumerate(lines):
        if pat.match(line.rstrip('\n')):
            new_lines = list(lines)
            del new_lines[i]
            # Remove double blank line
            if (i < len(new_lines) and i > 0
                    and new_lines[i - 1].strip() == ""
                    and new_lines[i].strip() == ""):
                del new_lines[i]
            filepath.write_text("".join(new_lines))
            return text
    return None


def restore_file(filepath: Path, original_text: str):
    """Restore a file to its original content."""
    filepath.write_text(original_text)


def bisect_remove(
    dag: DAG,
    candidates: list[str],
    check_modules: list[str],
    option: str,
    value: str,
    timeout: int,
) -> list[str]:
    """Binary-search remove options from candidates while check_modules build.

    Returns list of modules that must keep the option.
    """
    if not candidates:
        return []

    # Try removing all at once
    print(f"    Trying to remove all {len(candidates)} at once...", flush=True)
    originals: dict[str, str] = {}
    for mod in candidates:
        info = dag.modules.get(mod)
        if info is None:
            continue
        fp = dag.project_root / info.filepath
        orig = remove_option(fp, option, value)
        if orig is not None:
            originals[mod] = orig

    if lake_build_modules(check_modules, timeout):
        print(f"    All {len(candidates)} removed successfully!", flush=True)
        return []

    # Revert all
    for mod, orig in originals.items():
        info = dag.modules.get(mod)
        if info:
            restore_file(dag.project_root / info.filepath, orig)
    # Rebuild to restore oleans
    lake_build_modules(check_modules, timeout)

    if len(candidates) == 1:
        print(f"    Must keep: {candidates[0]}", flush=True)
        return candidates

    # Split and recurse
    mid = len(candidates) // 2
    left = candidates[:mid]
    right = candidates[mid:]

    print(f"    Bisecting: trying left half ({len(left)})...", flush=True)
    # Try removing left half
    left_originals: dict[str, str] = {}
    for mod in left:
        info = dag.modules.get(mod)
        if info is None:
            continue
        fp = dag.project_root / info.filepath
        orig = remove_option(fp, option, value)
        if orig is not None:
            left_originals[mod] = orig

    left_ok = lake_build_modules(check_modules, timeout)
    if not left_ok:
        # Revert left, some in left are needed
        for mod, orig in left_originals.items():
            info = dag.modules.get(mod)
            if info:
                restore_file(dag.project_root / info.filepath, orig)
        lake_build_modules(check_modules, timeout)
        needed_left = bisect_remove(dag, left, check_modules, option, value, timeout)
    else:
        needed_left = []

    # Now try right half (left removals that succeeded are still in effect)
    print(f"    Bisecting: trying right half ({len(right)})...", flush=True)
    right_originals: dict[str, str] = {}
    for mod in right:
        info = dag.modules.get(mod)
        if info is None:
            continue
        fp = dag.project_root / info.filepath
        orig = remove_option(fp, option, value)
        if orig is not None:
            right_originals[mod] = orig

    right_ok = lake_build_modules(check_modules, timeout)
    if not right_ok:
        # Revert right, some in right are needed
        for mod, orig in right_originals.items():
            info = dag.modules.get(mod)
            if info:
                restore_file(dag.project_root / info.filepath, orig)
        lake_build_modules(check_modules, timeout)
        needed_right = bisect_remove(dag, right, check_modules, option, value, timeout)
    else:
        needed_right = []

    return needed_left + needed_right


def main():
    parser = argparse.ArgumentParser(
        description="Fix non-local breakage by adding+minimizing set_option in deps"
    )
    parser.add_argument(
        "modules",
        nargs="+",
        help="Failing module names (e.g. Mathlib.Foo.Bar)",
    )
    parser.add_argument(
        "--option",
        default=DEFAULT_OPTION,
        help=f"Option name (default: {DEFAULT_OPTION})",
    )
    parser.add_argument(
        "--value",
        default="true",
        help="Value to set the option to (default: true)",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=600,
        help="Build timeout per module in seconds (default: 600)",
    )
    parser.add_argument(
        "--directories",
        nargs="+",
        default=None,
        help="Directories to scan when building the import DAG (default: '.')",
    )
    args = parser.parse_args()

    option = args.option
    value = args.value

    print("Building import DAG...", flush=True)
    dag = DAG.from_directories(PROJECT_DIR, args.directories)
    print(f"  {len(dag.modules)} modules parsed")

    check_modules = list(args.modules)

    # Step 1: collect all deps of all failing modules
    all_deps: set[str] = set()
    for mod in args.modules:
        all_deps |= collect_all_dependencies(dag, mod)

    # Step 2: add option to all deps that don't already have it
    added = []
    for d in sorted(all_deps):
        info = dag.modules.get(d)
        if info is None:
            continue
        fp = dag.project_root / info.filepath
        if not has_option(fp, option, value):
            if add_to_file(fp, option, value, dry_run=False):
                added.append(d)
    print(f"  Added option to {len(added)} dependencies of {len(args.modules)} modules",
          flush=True)

    # Step 3: verify all check modules build
    print(f"  Verifying build of {check_modules}...", flush=True)
    if not lake_build_modules(check_modules, args.timeout):
        print("  ERROR: modules still fail after adding option to all deps!")
        print("  Cannot proceed.")
        return

    print(f"  Build OK. Now minimizing {len(added)} additions...", flush=True)

    # Step 4: binary search remove unnecessary options
    needed = bisect_remove(dag, added, check_modules, option, value, args.timeout)

    removed_count = len(added) - len(needed)
    print(f"\n{'='*60}")
    print("RESULT")
    print(f"{'='*60}")
    print(f"  Check modules:       {len(check_modules)}")
    print(f"  Dependencies added:  {len(added)}")
    print(f"  Removed (unnecessary): {removed_count}")
    print(f"  Kept (needed):       {len(needed)}")
    if needed:
        print("\n  Needed modules:")
        for n in needed:
            print(f"    - {n}")


if __name__ == "__main__":
    main()
