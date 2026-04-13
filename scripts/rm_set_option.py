#!/usr/bin/env python3
"""
Remove unnecessary `set_option ... false in` from Mathlib.

Tries removing each occurrence (that isn't followed by a comment), testing
whether the file still builds. Processes files in reverse import-DAG order
(downstream first) to minimize unnecessary rebuilds.
"""

import argparse
import hashlib
import json
import re
import subprocess
import time
from dataclasses import dataclass
from pathlib import Path
from threading import Lock
from typing import Callable

from dag_traversal import (
    DAG,
    DAGTraverser,
    Display,
)
from set_option_utils import (
    DEFAULT_OPTIONS,
    PROJECT_DIR,
    commented_pattern,
    lake_build_with_progress,
    lakefile_pattern,
    removable_pattern,
)


PROGRESS_FILE = PROJECT_DIR / "scripts" / ".rm_set_option_progress.jsonl"

_progress_lock = Lock()


def _current_toolchain() -> str:
    return (PROJECT_DIR / "lean-toolchain").read_text().strip()


def file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_progress() -> dict[str, str] | None:
    """Load progress file. Returns {module: sha256} or None if invalid/missing."""
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
    """Write toolchain header to a fresh progress file."""
    with open(PROGRESS_FILE, "w") as f:
        json.dump({"toolchain": _current_toolchain()}, f)
        f.write("\n")


def save_progress(module: str, sha256: str):
    """Append a completion record (thread-safe)."""
    with _progress_lock:
        with open(PROGRESS_FILE, "a") as f:
            json.dump({"module": module, "sha256": sha256}, f)
            f.write("\n")


@dataclass
class FileResult:
    """Result of processing one file."""

    removable: int = 0  # lines we attempted to remove
    removed: int = 0  # successfully removed
    kept: int = 0  # had to keep (build failed)
    skipped: int = 0  # with trailing comments


@dataclass
class Summary:
    """Aggregated results."""

    total_files: int = 0
    files_fully_cleaned: int = 0
    files_partially_cleaned: int = 0
    files_unchanged: int = 0
    files_errored: int = 0
    total_removed: int = 0
    total_kept: int = 0
    total_skipped: int = 0
    duration: float = 0.0


class _RemoveDisplay(Display):
    """Progress display for the remove script."""

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
                self.total_removed += result.removed
                self.total_kept += result.kept
                if result.removed > 0 and result.kept == 0:
                    sym = "\u2713"
                elif result.removed > 0:
                    sym = "~"
                else:
                    sym = "\u00b7"
                parts = []
                if result.removed:
                    parts.append(f"-{result.removed}")
                if result.kept:
                    parts.append(f"kept {result.kept}")
                if result.skipped:
                    parts.append(f"skipped {result.skipped}")
                detail = " ".join(parts)
                self.messages.append(f"  {sym} {module_name} {detail}")
            elif error:
                self.messages.append(f"  ! {module_name}: {error}")
            self._redraw()


def handle_lakefile(options: list[str]) -> bool:
    """Check and remove options from lakefile.lean. Returns True if changed."""
    lakefile = PROJECT_DIR / "lakefile.lean"
    content = lakefile.read_text()
    changed = False
    for opt in options:
        if opt not in content:
            continue
        pat = lakefile_pattern(opt)
        new_content = pat.sub("", content)
        if new_content != content:
            content = new_content
            changed = True
            print(f"Removed {opt} from lakefile.lean")
    if changed:
        lakefile.write_text(content)
    return changed


def scan_files(dag: DAG, options: list[str]) -> dict[str, list[int]]:
    """Find files with removable set_option lines.

    Returns dict of module_name -> list of 0-indexed line numbers.
    """
    removable_pats = [removable_pattern(opt) for opt in options]
    commented_pats = [commented_pattern(opt) for opt in options]
    results: dict[str, list[int]] = {}
    for name, info in dag.modules.items():
        filepath = dag.project_root / info.filepath
        if not filepath.exists():
            continue
        lines = filepath.read_text().splitlines(keepends=True)
        removable = []
        for i, line in enumerate(lines):
            if any(p.match(line) for p in commented_pats):
                continue
            if any(p.match(line) for p in removable_pats):
                removable.append(i)
        if removable:
            results[name] = removable
    return results


def count_skipped(filepath: Path, options: list[str]) -> int:
    """Count set_option lines with trailing comments."""
    commented_pats = [commented_pattern(opt) for opt in options]
    count = 0
    for line in filepath.read_text().splitlines():
        if any(p.match(line) for p in commented_pats):
            count += 1
    return count


def initial_build():
    """Run a full lake build so all .oleans are fresh.

    Without this, every worker would redundantly rebuild shared
    upstream modules.
    """
    print("Running initial build...", flush=True)
    returncode, _ = lake_build_with_progress(PROJECT_DIR)
    if returncode != 0:
        print("  (initial build had errors — continuing anyway)")


def make_process_file(
    removable_map: dict[str, list[int]],
    options: list[str],
    timeout: int,
    traverser: DAGTraverser,
) -> Callable:
    """Create the per-file action callback."""

    def process_file(module_name: str, filepath: Path) -> FileResult:
        abs_path = filepath
        removable_lines = removable_map.get(module_name, [])
        skipped = count_skipped(abs_path, options)

        if not removable_lines:
            save_progress(module_name, file_sha256(abs_path))
            return FileResult(skipped=skipped)

        original_text = abs_path.read_text()
        original = original_text.splitlines(keepends=True)

        traverser.inflight_register(abs_path, original_text)

        try:
            # Phase 1: try removing ALL at once
            removable_set = set(removable_lines)
            new_lines = [line for i, line in enumerate(original) if i not in removable_set]
            abs_path.write_text("".join(new_lines))

            ok, _ = traverser.lake_build(module_name, PROJECT_DIR, timeout)
            if ok:
                save_progress(module_name, file_sha256(abs_path))
                return FileResult(
                    removable=len(removable_lines),
                    removed=len(removable_lines),
                    skipped=skipped,
                )

            # Phase 2: revert, then one-at-a-time bottom-to-top
            abs_path.write_text(original_text)
            current = list(original)
            removed = 0
            kept = 0

            for line_idx in reversed(removable_lines):
                test = current[:line_idx] + current[line_idx + 1 :]
                abs_path.write_text("".join(test))

                ok, _ = traverser.lake_build(module_name, PROJECT_DIR, timeout)
                if ok:
                    current = test
                    removed += 1
                else:
                    abs_path.write_text("".join(current))
                    kept += 1

            save_progress(module_name, file_sha256(abs_path))
            return FileResult(
                removable=len(removable_lines),
                removed=removed,
                kept=kept,
                skipped=skipped,
            )
        except BaseException:
            abs_path.write_text(original_text)
            raise
        finally:
            traverser.inflight_unregister(abs_path)

    return process_file


def print_summary(summary: Summary):
    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"  Files processed:        {summary.total_files}")
    print(f"  Fully cleaned:          {summary.files_fully_cleaned}")
    print(f"  Partially cleaned:      {summary.files_partially_cleaned}")
    print(f"  Unchanged:              {summary.files_unchanged}")
    print(f"  Errors:                 {summary.files_errored}")
    print(f"  Lines removed:          {summary.total_removed}")
    print(f"  Lines kept:             {summary.total_kept}")
    print(f"  Lines skipped (comment):{summary.total_skipped}")
    print(f"  Duration:               {summary.duration:.0f}s")


def main():
    parser = argparse.ArgumentParser(
        description="Remove unnecessary set_option ... false in lines"
    )
    parser.add_argument(
        "--option",
        help="Only scan/remove this specific option (default: all known options)",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Scan and report without modifying files or building",
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
        "--files",
        nargs="*",
        help="Only process these files (paths relative to project root)",
    )
    parser.add_argument(
        "--no-initial",
        action="store_true",
        help="Skip the initial lake build (assumes .oleans are already fresh)",
    )
    parser.add_argument(
        "--no-resume",
        action="store_true",
        help="Ignore progress from a previous interrupted run",
    )
    args = parser.parse_args()

    options = [args.option] if args.option else DEFAULT_OPTIONS

    start_time = time.time()

    # Step 1: lakefile
    if not args.dry_run:
        handle_lakefile(options)

    # Step 2: build DAG
    print("Building import DAG...", flush=True)
    full_dag = DAG.from_directories(PROJECT_DIR)
    print(f"  {len(full_dag.modules)} modules parsed")

    # Step 3: scan for removable lines
    print("Scanning for removable set_option lines...", flush=True)
    removable_map = scan_files(full_dag, options)

    if args.files:
        # Filter to requested files
        requested = set()
        for f in args.files:
            mod = f.replace("/", ".").removesuffix(".lean")
            requested.add(mod)
        removable_map = {k: v for k, v in removable_map.items() if k in requested}

    total_removable = sum(len(v) for v in removable_map.values())
    print(f"  {len(removable_map)} files with {total_removable} removable lines")

    # Step 3b: filter out modules completed in a previous run
    resumed = 0
    if not args.no_resume:
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
                total_removable = sum(len(v) for v in removable_map.values())
                print(f"  Resuming: skipped {resumed} already-processed modules"
                      f" ({len(removable_map)} remaining, {total_removable} lines)")

    if not removable_map:
        print("Nothing to do.")
        if PROGRESS_FILE.exists():
            PROGRESS_FILE.unlink()
        return

    # Step 4: initial build to ensure all .oleans are fresh
    if not args.dry_run and not args.no_initial:
        initial_build()

    # Step 5: traverse full DAG, skipping modules without removable lines.
    # We use the full DAG (not a subset) to ensure the backward traversal
    # respects all import edges.  Without this, two modules in the target
    # set that are connected through intermediate non-target modules could
    # be processed concurrently, causing `lake build` to race on rebuilding
    # shared upstream .oleans.
    target_modules = set(removable_map.keys())
    skip_modules = set(full_dag.modules.keys()) - target_modules

    # Weight = LOC × number of removable lines, so expensive files get
    # critical-path priority in the DAG traversal scheduler.
    weights = {}
    for name, removable_lines in removable_map.items():
        fp = full_dag.project_root / full_dag.modules[name].filepath
        loc = len(fp.read_text().splitlines())
        weights[name] = loc * len(removable_lines)

    if args.dry_run:
        sub_dag = full_dag.subset(target_modules)
        levels = sub_dag.levels_backward()
        print(f"\nBackward traversal: {len(levels)} levels")
        for i, level in enumerate(levels):
            count = sum(len(removable_map.get(m, [])) for m in level)
            print(f"  Level {i}: {len(level)} files, {count} removable lines")
        print(f"\nTotal: {len(removable_map)} files, {total_removable} lines")
        print("(dry run — no changes made)")
        return

    # Initialize progress file (preserves existing entries on resume)
    if not PROGRESS_FILE.exists() or resumed == 0:
        init_progress()

    traverser = DAGTraverser()
    display = _RemoveDisplay()
    action = make_process_file(removable_map, options, args.timeout, traverser)

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
            weights=weights,
        )
    except KeyboardInterrupt:
        display.stop()
        print("\nInterrupted. Press Ctrl-C again if the process doesn't exit.", flush=True)
        traverser.force_exit(1)
    finally:
        display.stop()

    # Step 6: summarize (only count target modules, not skipped ones)
    target_results = [tr for tr in results if tr.module_name in target_modules]
    summary = Summary(total_files=len(target_results), duration=time.time() - start_time)

    for tr in target_results:
        r: FileResult | None = tr.result
        if tr.error:
            summary.files_errored += 1
            continue
        if r is None:
            continue
        summary.total_removed += r.removed
        summary.total_kept += r.kept
        summary.total_skipped += r.skipped
        if r.removed > 0 and r.kept == 0:
            summary.files_fully_cleaned += 1
        elif r.removed > 0:
            summary.files_partially_cleaned += 1
        else:
            summary.files_unchanged += 1

    print_summary(summary)

    # Clean up progress file on successful complete run
    if summary.files_errored == 0 and PROGRESS_FILE.exists():
        PROGRESS_FILE.unlink()
        print("  (progress file cleaned up)")


if __name__ == "__main__":
    main()
