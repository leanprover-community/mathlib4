#!/usr/bin/env python3
"""
Remove unnecessary module-level `set_option` lines from a Lean project.

Traverses the import DAG **backward** (downstream first) so removing an
option from an upstream file doesn't invalidate cached .oleans of already-
processed downstream files.

For each file that contains the target line, tries removing it and building
the module.  If the build succeeds the line stays removed; otherwise it is
restored.

To use outside mathlib, copy `rm_module_set_option.py`, `dag_traversal.py` and
`set_option_utils.py` to a subdirectory of your project named `scripts/` and
then run from the project root with `scripts/rm_module_set_option.py`.  Pass
`--directories <root>` if your source files aren't directly under the project
root.

Usage:
    python3 scripts/rm_module_set_option.py [--option NAME] [--dry-run] [--resume] ...
"""

import argparse
import hashlib
import json
import os
import re
import time
from dataclasses import dataclass
from pathlib import Path
from threading import Lock

try:
    from dag_traversal import (
        DAG,
        DAGTraverser,
        Display,
        ShutdownError,
    )
    from set_option_utils import (
        PROJECT_DIR,
        lake_build_with_progress,
    )
except ImportError as _e:
    raise SystemExit(
        f"error: {_e}\n\n"
        f"  This script depends on sibling Python files in {Path(__file__).parent}:\n"
        "    - dag_traversal.py\n"
        "    - set_option_utils.py\n"
        "  These are mathlib scripts, not pip packages.  Copy them into your\n"
        "  `scripts/` directory alongside this script."
    )

DEFAULT_OPTION = "backward.defeq.atInstanceTransparency"

PROGRESS_FILE = PROJECT_DIR / "scripts" / ".rm_module_set_option_progress.jsonl"

_progress_lock = Lock()


def _current_toolchain() -> str:
    return (PROJECT_DIR / "lean-toolchain").read_text().strip()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_progress() -> dict[str, str] | None:
    """Load progress file. Returns {module: sha256} or None if invalid."""
    if not PROGRESS_FILE.exists():
        return None
    progress: dict[str, str] = {}
    toolchain = _current_toolchain()
    with open(PROGRESS_FILE) as f:
        for i, line in enumerate(f):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue
            if i == 0:
                if record.get("toolchain") != toolchain:
                    return None
                continue
            if "module" in record and "sha256" in record:
                progress[record["module"]] = record["sha256"]
    return progress


def init_progress():
    with open(PROGRESS_FILE, "w") as f:
        json.dump({"toolchain": _current_toolchain()}, f)
        f.write("\n")


def save_progress(module: str, sha256: str):
    with _progress_lock:
        with open(PROGRESS_FILE, "a") as f:
            json.dump({"module": module, "sha256": sha256}, f)
            f.write("\n")


def module_set_option_pattern(option: str, value: str = "false") -> re.Pattern:
    """Match module-level `set_option <option> <value>` (no trailing `in`)."""
    escaped = re.escape(option)
    escaped_val = re.escape(value)
    return re.compile(rf"^set_option {escaped} {escaped_val}\s*$")


@dataclass
class FileResult:
    removed: bool = False
    kept: bool = False


class _RemoveDisplay(Display):
    def __init__(self):
        super().__init__()
        self.total_removed = 0
        self.total_kept = 0

    def _status_line(self) -> str:
        return (
            f"[{self.completed}/{self.total}]  "
            f"Working on: {self.inflight}  "
            f"Removed: {self.total_removed}  Kept: {self.total_kept}"
        )

    def on_module(self, module_name: str, result: FileResult | None, error: Exception | None):
        with self.lock:
            if result:
                if result.removed:
                    self.total_removed += 1
                    sym = "\u2713"
                elif result.kept:
                    self.total_kept += 1
                    sym = "x"
                else:
                    sym = "\u00b7"
                detail = "removed" if result.removed else ("kept" if result.kept else "")
                self.messages.append(f"  {sym} {module_name} {detail}")
            elif error:
                self.messages.append(f"  ! {module_name}: {error}")
            self._redraw()


def scan_files(dag: DAG, option: str, value: str = "false") -> dict[str, int]:
    """Find files with the module-level set_option line.

    Returns dict of module_name -> 0-indexed line number.
    """
    pat = module_set_option_pattern(option, value)
    results: dict[str, int] = {}
    for name, info in dag.modules.items():
        filepath = dag.project_root / info.filepath
        if not filepath.exists():
            continue
        for i, line in enumerate(filepath.read_text().splitlines()):
            if pat.match(line):
                results[name] = i
                break
    return results


def _collect_all_dependents(dag: DAG, module_name: str) -> list[str]:
    """Collect all transitive reverse dependencies (importers) of a module."""
    collected_set: set[str] = set()
    collected: list[str] = []
    frontier = {module_name}
    while frontier:
        next_frontier: set[str] = set()
        for mod in frontier:
            info = dag.modules.get(mod)
            if info is None:
                continue
            for imp in info.importers:
                if imp not in collected_set and imp != module_name:
                    collected_set.add(imp)
                    collected.append(imp)
                    next_frontier.add(imp)
        frontier = next_frontier
    return collected


def _collect_all_dependencies(dag: DAG, module_name: str) -> set[str]:
    """Collect all transitive dependencies (imports) of a module."""
    collected: set[str] = set()
    frontier = {module_name}
    while frontier:
        next_frontier: set[str] = set()
        for mod in frontier:
            info = dag.modules.get(mod)
            if info is None:
                continue
            for imp in info.imports:
                if imp not in collected and imp != module_name:
                    collected.add(imp)
                    next_frontier.add(imp)
        frontier = next_frontier
    return collected


def make_process_file(
    removable_map: dict[str, int],
    timeout: int,
    traverser: DAGTraverser,
    dag: DAG | None = None,
    build_dependents: bool = False,
    check_modules: list[str] | None = None,
):
    def process_file(module_name: str, filepath: Path) -> FileResult:
        if module_name not in removable_map:
            save_progress(module_name, file_sha256(filepath))
            return FileResult()

        line_idx = removable_map[module_name]
        original_text = filepath.read_text()
        lines = original_text.splitlines(keepends=True)

        traverser.inflight_register(filepath, original_text)
        try:
            # Remove the set_option line and any following blank line
            new_lines = list(lines)
            del new_lines[line_idx]
            # If removal left a double blank line, remove one
            if (line_idx < len(new_lines) and line_idx > 0
                    and new_lines[line_idx - 1].strip() == ""
                    and new_lines[line_idx].strip() == ""):
                del new_lines[line_idx]

            filepath.write_text("".join(new_lines))

            # Build the module itself
            ok, _ = traverser.lake_build(module_name, PROJECT_DIR, timeout)

            # Build specific check modules if requested
            if ok and check_modules:
                for cm in check_modules:
                    if traverser.shutdown_event.is_set():
                        break
                    cm_ok, _ = traverser.lake_build(cm, PROJECT_DIR, timeout)
                    if not cm_ok:
                        ok = False
                        break

            # Also build dependents (reverse dependencies) if requested
            if ok and build_dependents and dag is not None:
                dependents = _collect_all_dependents(dag, module_name)
                for dep in dependents:
                    if traverser.shutdown_event.is_set():
                        break
                    dep_ok, _ = traverser.lake_build(dep, PROJECT_DIR, timeout)
                    if not dep_ok:
                        ok = False
                        break

            if ok:
                save_progress(module_name, file_sha256(filepath))
                return FileResult(removed=True)

            # Revert
            filepath.write_text(original_text)
            # Rebuild the module with the option restored so oleans are correct
            traverser.lake_build(module_name, PROJECT_DIR, timeout)
            save_progress(module_name, file_sha256(filepath))
            return FileResult(kept=True)
        except BaseException:
            filepath.write_text(original_text)
            raise
        finally:
            traverser.inflight_unregister(filepath)

    return process_file


def main():
    parser = argparse.ArgumentParser(
        description="Remove unnecessary module-level set_option lines"
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
        help="Scan and report without modifying files",
    )
    parser.add_argument(
        "--max-workers",
        type=int,
        default=None,
        help="Max parallel workers (default: cpu_count)",
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
    parser.add_argument(
        "--no-initial",
        action="store_true",
        help="Skip the initial lake build",
    )
    parser.add_argument(
        "--resume",
        action="store_true",
        help="Resume from previous run",
    )
    parser.add_argument(
        "--build-dependents",
        action="store_true",
        help="After removing the option, also build all transitive reverse "
             "dependencies (importers). Catches non-local breakage from "
             "option removal.",
    )
    parser.add_argument(
        "--files",
        nargs="*",
        help="Only process these files",
    )
    parser.add_argument(
        "--deps-of",
        nargs="*",
        metavar="MODULE",
        help="Only process transitive dependencies of these modules "
             "(module names like Mathlib.Foo.Bar)",
    )
    parser.add_argument(
        "--check-module",
        nargs="*",
        metavar="MODULE",
        help="After removing an option, also build these modules to verify "
             "they still work (module names like Mathlib.Foo.Bar)",
    )
    args = parser.parse_args()

    option = args.option
    start_time = time.time()

    # Build DAG
    print("Building import DAG...", flush=True)
    full_dag = DAG.from_directories(PROJECT_DIR, args.directories)
    print(f"  {len(full_dag.modules)} modules parsed")

    # Scan for removable lines
    print("Scanning for module-level set_option lines...", flush=True)
    removable_map = scan_files(full_dag, option, args.value)

    if args.files:
        requested = set()
        for f in args.files:
            mod = f.replace("/", ".").removesuffix(".lean")
            requested.add(mod)
        removable_map = {k: v for k, v in removable_map.items() if k in requested}

    if args.deps_of:
        deps_set: set[str] = set()
        for mod in args.deps_of:
            deps_set |= _collect_all_dependencies(full_dag, mod)
        removable_map = {k: v for k, v in removable_map.items() if k in deps_set}

    print(f"  {len(removable_map)} files with the option set")

    # Resume filtering
    resumed = 0
    if args.resume:
        progress = load_progress()
        if progress:
            to_skip = []
            for name in list(removable_map):
                if name in progress:
                    fp = full_dag.project_root / full_dag.modules[name].filepath
                    if fp.exists() and file_sha256(fp) == progress[name]:
                        to_skip.append(name)
            for name in to_skip:
                del removable_map[name]
            resumed = len(to_skip)
            if resumed:
                print(f"  Resuming: skipped {resumed} already-processed modules"
                      f" ({len(removable_map)} remaining)")

    if not removable_map:
        print("Nothing to do.")
        return

    if args.dry_run:
        print(f"\n{len(removable_map)} files would be tested for removal")
        print("(dry run — no changes made)")
        return

    # Initial build
    if not args.no_initial:
        print("Running initial build...", flush=True)
        returncode, _ = lake_build_with_progress(PROJECT_DIR)
        if returncode != 0:
            print("  (initial build had errors — continuing anyway)")

    # Initialize progress
    if not PROGRESS_FILE.exists() or resumed == 0:
        init_progress()

    # Traverse backward
    target_modules = set(removable_map.keys())
    skip_modules = set(full_dag.modules.keys()) - target_modules

    traverser = DAGTraverser()
    display = _RemoveDisplay()
    action = make_process_file(
        removable_map, args.timeout, traverser,
        dag=full_dag, build_dependents=args.build_dependents,
        check_modules=args.check_module,
    )

    display.start(len(full_dag.modules))
    try:
        results = traverser.traverse(
            full_dag,
            action,
            direction="backward",
            max_workers=args.max_workers,
            progress_callback=display.on_progress,
            module_callback=display.on_module,
            skip=skip_modules,
        )
    except KeyboardInterrupt:
        display.stop()
        print("\nInterrupted.", flush=True)
        traverser.force_exit(1)
    finally:
        display.stop()

    # Summary
    target_results = [tr for tr in results if tr.module_name in target_modules]
    total_removed = sum(1 for tr in target_results if tr.result and tr.result.removed)
    total_kept = sum(1 for tr in target_results if tr.result and tr.result.kept)
    errors = sum(1 for tr in target_results if tr.error)
    duration = time.time() - start_time

    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"  Files tested:     {len(target_results)}")
    print(f"  Option removed:   {total_removed}")
    print(f"  Option kept:      {total_kept}")
    print(f"  Errors:           {errors}")
    print(f"  Duration:         {duration:.0f}s")

    if errors:
        print("\nErrors:")
        for tr in target_results:
            if tr.error:
                print(f"  {tr.module_name}: {tr.error}")

    # Clean up progress
    if errors == 0 and PROGRESS_FILE.exists():
        PROGRESS_FILE.unlink()
        print("  (progress file cleaned up)")


if __name__ == "__main__":
    main()
