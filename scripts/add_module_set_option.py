#!/usr/bin/env python3
"""
Add module-level `set_option` lines to every Lean file in the project.

Inserts `set_option <option> false` (module-scoped, no `in`) after the last
import line in each .lean file in the project.  Also removes the corresponding
entry from lakefile.lean if present.

To use outside mathlib, copy `add_module_set_option.py`, `dag_traversal.py` and
`set_option_utils.py` to a subdirectory of your project named `scripts/` and
then run from the project root with `scripts/add_module_set_option.py`.  Pass
`--directories <root>` if your source files aren't directly under the project
root.

Usage:
    python3 scripts/add_module_set_option.py [--option NAME] [--dry-run]
"""

import argparse
import re
import sys
from pathlib import Path

from set_option_utils import PROJECT_DIR, lakefile_pattern

DEFAULT_OPTION = "backward.defeq.atInstanceTransparency"


def find_insert_point(lines: list[str]) -> int:
    """Find the line index after imports and module docstring.

    Inserts after the module docstring (/-! ... -/) if present right after
    imports, otherwise after the last import. The linter requires the module
    docstring to be the first command after imports, so set_option must come
    after it.

    Falls back to after `module` if no imports, or line 0.
    """
    import_re = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s")
    last_import = -1
    module_line = -1
    in_block_comment = False
    for i, line in enumerate(lines):
        stripped = line.strip()
        # Track block comments
        if in_block_comment:
            if "-/" in stripped:
                in_block_comment = False
            continue
        if stripped.startswith("/-"):
            if "-/" not in stripped[2:]:
                in_block_comment = True
            continue
        # Track module line
        if stripped == "module" or stripped.startswith("module ") or stripped.startswith("module\t"):
            module_line = i
            continue
        # Skip blank lines and line comments
        if stripped == "" or stripped.startswith("--"):
            continue
        # Check for import
        if import_re.match(stripped):
            last_import = i
            continue
        # Any other content after we've seen imports means header is done
        if last_import >= 0:
            break
    if last_import < 0:
        if module_line >= 0:
            return module_line + 1
        return 0
    # We have the last import at last_import. Now look for a module docstring
    # (/-! ... -/) immediately following (possibly separated by blank lines).
    idx = last_import + 1
    # Skip blank lines
    while idx < len(lines) and lines[idx].strip() == "":
        idx += 1
    # Check for module docstring
    if idx < len(lines) and lines[idx].strip().startswith("/-!"):
        # Find the end of this block comment
        if "-/" in lines[idx].strip()[3:]:
            # Single-line module docstring
            return idx + 1
        # Multi-line: scan for closing -/
        idx += 1
        while idx < len(lines):
            if "-/" in lines[idx]:
                return idx + 1
            idx += 1
    # No module docstring, insert after imports
    return last_import + 1


def add_to_file(filepath: Path, option: str, value: str, dry_run: bool) -> bool:
    """Add module-level set_option to a file. Returns True if modified."""
    text = filepath.read_text()
    line = f"set_option {option} {value}"

    # Skip if already present as a module-level option (not `set_option ... in`)
    if re.search(rf"^{re.escape(line)}$", text, re.MULTILINE):
        return False

    lines = text.splitlines(keepends=True)
    idx = find_insert_point(lines)

    # Insert a blank line + the set_option + blank line
    insert = f"\n{line}\n"
    # If there's already a blank line after imports, don't double-blank
    if idx < len(lines) and lines[idx].strip() == "":
        insert = f"{line}\n"

    new_lines = lines[:idx] + [insert] + lines[idx:]

    if not dry_run:
        filepath.write_text("".join(new_lines))
    return True


def main():
    parser = argparse.ArgumentParser(
        description="Add module-level set_option to every Lean file in the project."
    )
    parser.add_argument(
        "--option",
        default=DEFAULT_OPTION,
        help=f"Option name (default: {DEFAULT_OPTION})",
    )
    parser.add_argument(
        "--value",
        default="false",
        help="Value of the option (default: false)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Report without modifying files",
    )
    parser.add_argument(
        "--directories",
        nargs="+",
        default=None,
        help="Directories to scan for .lean files (default: '.')",
    )
    parser.add_argument(
        "--deps-of",
        nargs="*",
        metavar="MODULE",
        help="Only add to transitive dependencies of these modules "
             "(module names like Mathlib.Foo.Bar)",
    )
    parser.add_argument(
        "--no-lakefile",
        action="store_true",
        help="Skip removing the option from lakefile.lean",
    )
    args = parser.parse_args()

    option = args.option

    # Step 1: remove from lakefile
    if not args.no_lakefile:
        lakefile = PROJECT_DIR / "lakefile.lean"
        if lakefile.exists():
            content = lakefile.read_text()
            pat = lakefile_pattern(option, args.value)
            new_content = pat.sub("", content)
            if new_content != content:
                if not args.dry_run:
                    lakefile.write_text(new_content)
                print(f"Removed {option} from lakefile.lean")

    # Step 2: determine which files to process via the import DAG
    sys.path.insert(0, str(Path(__file__).parent))
    from dag_traversal import DAG

    dag = DAG.from_directories(PROJECT_DIR, args.directories)

    if args.deps_of:
        deps_set: set[str] = set()
        for mod in args.deps_of:
            # Collect transitive dependencies
            frontier = {mod}
            visited: set[str] = set()
            while frontier:
                next_frontier: set[str] = set()
                for m in frontier:
                    info = dag.modules.get(m)
                    if info is None:
                        continue
                    for imp in info.imports:
                        if imp not in visited and imp != mod:
                            visited.add(imp)
                            next_frontier.add(imp)
                frontier = next_frontier
            deps_set |= visited
        files = []
        for name in sorted(deps_set):
            info = dag.modules.get(name)
            if info:
                fp = dag.project_root / info.filepath
                if fp.exists():
                    files.append(fp)
        print(f"  {len(files)} dependencies of {', '.join(args.deps_of)}")
    else:
        files = []
        for name in sorted(dag.modules):
            info = dag.modules[name]
            fp = dag.project_root / info.filepath
            if fp.exists():
                files.append(fp)

    modified = 0
    for filepath in files:
        if add_to_file(filepath, option, args.value, args.dry_run):
            modified += 1

    action = "Would modify" if args.dry_run else "Modified"
    print(f"{action} {modified}/{len(files)} files")


if __name__ == "__main__":
    main()
