#!/usr/bin/env python3
"""
Add `set_option ... false in` before failing declarations.

Traverses the import DAG forward (roots first) so that each module is only
built after all its imports are clean.  No "discovery" builds needed.
"""

import argparse
import platform
import re
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from threading import Lock
from typing import Callable

from dag_traversal import (
    DAG,
    DAGTraverser,
    Display,
    TraversalResult,
)
from set_option_utils import (
    DEFAULT_OPTIONS,
    PROJECT_DIR,
    lake_build_with_progress,
    set_option_line,
)


@dataclass
class FileResult:
    """Result of processing one file."""

    fixed: int = 0
    already_present: int = 0


def _opener_cmd() -> list[str]:
    """Return the platform-appropriate file-open command."""
    import shutil

    system = platform.system()
    if system == "Darwin":
        return ["open"]
    elif system == "Windows":
        return ["start"]
    # Linux: prefer code, then xdg-open
    if shutil.which("code"):
        return ["code", "--goto"]
    if shutil.which("xdg-open"):
        return ["xdg-open"]
    return ["open"]


class _AddDisplay(Display):
    """Progress display for the add script."""

    def __init__(self, dag: DAG, open_on_failure: bool = False):
        super().__init__()
        self.dag = dag
        self.total_fixed = 0
        self.total_failed = 0
        self.open_on_failure = open_on_failure

    def _status_line(self) -> str:
        return (
            f"[{self.completed}/{self.total}]  "
            f"Working on: {self.inflight}  "
            f"Fixed: {self.total_fixed}  Failed: {self.total_failed}"
        )

    def on_module(self, module_name: str, result: FileResult | None, error: Exception | None):
        with self.lock:
            if result:
                self.total_fixed += result.fixed
                if result.fixed > 0:
                    sym = "+"
                else:
                    sym = "·"
                detail = f"+{result.fixed}" if result.fixed else ""
                if result.already_present:
                    detail += f" already {result.already_present}"
                self.messages.append(f"  {sym} {module_name} {detail}")
            elif error:
                self.total_failed += 1
                self.messages.append(f"  ! {module_name}: {error}")
                if self.open_on_failure:
                    info = self.dag.modules.get(module_name)
                    if info:
                        filepath = str(info.filepath)
                        subprocess.Popen(_opener_cmd() + [filepath], cwd=PROJECT_DIR)
            self._redraw()


def is_inside_block_comment(lines: list[str], line_idx: int) -> bool:
    """Check if line_idx is inside a /- ... -/ block comment."""
    for i in range(line_idx - 1, -1, -1):
        line = lines[i]
        if "/-" in line:
            start_pos = line.find("/-")
            end_pos = line.find("-/", start_pos + 2)
            if end_pos == -1:
                return True
            return False
        if "-/" in line:
            return False
    return False


def find_declaration_start(lines: list[str], error_line: int) -> int:
    """Find the start of the declaration containing the error.

    Walks backwards from error_line (1-indexed) to the first blank line
    that isn't inside a block comment.

    TODO: This heuristic is imperfect — it can misidentify the declaration
    boundary when there's no blank line between consecutive declarations,
    or when multi-line attributes bridge two declarations. Ideas for a
    better rule welcome.
    """
    idx = error_line - 1  # convert to 0-indexed

    while idx > 0:
        idx -= 1
        if lines[idx].strip() == "":
            if not is_inside_block_comment(lines, idx):
                return idx + 1

    return 0


# lake build outputs "error: filepath:line:col: message"
LAKE_ERROR_PATTERN = re.compile(r"^error: (.+?\.lean):(\d+):\d+:", re.MULTILINE)


def parse_errors_in_file(build_output: str, filepath: Path) -> list[int]:
    """Parse error line numbers for a specific file from build output."""
    filepath_str = str(filepath)
    error_lines: list[int] = []
    for match in LAKE_ERROR_PATTERN.finditer(build_output):
        if match.group(1) == filepath_str:
            line_num = int(match.group(2))
            if line_num not in error_lines:
                error_lines.append(line_num)
    error_lines.sort()
    return error_lines


def parse_error_modules(build_output: str) -> set[str]:
    """Parse module names of all files with errors from build output."""
    modules: set[str] = set()
    for match in LAKE_ERROR_PATTERN.finditer(build_output):
        filepath = match.group(1)
        module = filepath.replace("/", ".").removesuffix(".lean")
        modules.add(module)
    return modules


def count_errors_per_module(build_output: str) -> dict[str, int]:
    """Count errors per module from build output."""
    counts: dict[str, int] = {}
    for match in LAKE_ERROR_PATTERN.finditer(build_output):
        module = match.group(1).replace("/", ".").removesuffix(".lean")
        counts[module] = counts.get(module, 0) + 1
    return counts


def initial_build() -> tuple[set[str], str]:
    """Run a full lake build to discover which modules have errors.

    Returns (error_modules, build_output).
    """
    print("Running initial build...", flush=True)
    _, output = lake_build_with_progress(PROJECT_DIR)
    error_mods = parse_error_modules(output)
    print(f"  {len(error_mods)} modules with errors")
    return error_mods, output


class UnfixableError(Exception):
    """Raised when errors remain that can't be fixed by set_option insertion."""

    def __init__(self, msg: str, output: str = ""):
        self.output = output
        super().__init__(msg)


def make_process_module(
    options: list[str],
    timeout: int,
    traverser: DAGTraverser,
) -> Callable:
    """Create the per-module action callback."""

    # Thread-safe last-successful combination, shared across modules.
    _last_lock = Lock()
    _last: list[str] = [options[0]]

    def _get_last() -> list[str]:
        with _last_lock:
            return list(_last)

    def _set_last(combo: list[str]):
        nonlocal _last
        with _last_lock:
            _last = list(combo)

    def options_present_at(lines: list[str], decl_start: int) -> set[str]:
        """Return which managed options already appear at decl_start onward.

        Scans forward from decl_start through consecutive set_option lines
        (which precede the actual declaration keyword).
        """
        present: set[str] = set()
        idx = decl_start
        while idx < len(lines):
            found = False
            for opt in options:
                needle = set_option_line(opt).strip()
                if needle in lines[idx]:
                    present.add(opt)
                    found = True
                    break
            if not found:
                break
            idx += 1
        return present

    def candidates(missing: list[str]) -> list[list[str]]:
        """Generate candidate combinations from missing options.

        Tries last_successful (filtered to missing) first, then each single
        missing option, then all missing options together.
        """
        seen: list[list[str]] = []
        # Last successful, filtered to only missing options
        ls_filtered = [opt for opt in _get_last() if opt in missing]
        if ls_filtered:
            seen.append(ls_filtered)
        for opt in missing:
            combo = [opt]
            if combo not in seen:
                seen.append(combo)
        if len(missing) > 1 and missing not in seen:
            seen.append(list(missing))
        return seen

    def process_module(module_name: str, filepath: Path) -> FileResult:
        rel_path = filepath.relative_to(PROJECT_DIR)

        # Initial build
        ok, output = traverser.lake_build(module_name, PROJECT_DIR, timeout)
        if ok:
            return FileResult()

        error_lines = parse_errors_in_file(output, rel_path)
        if not error_lines:
            # Errors are in other files, not ours — treat as success
            return FileResult()

        original_text = filepath.read_text()
        lines = original_text.splitlines(keepends=True)
        fixed = 0
        already_present = 0

        traverser.inflight_register(filepath, original_text)

        try:
            # Process errors first-to-last. After each insertion, line numbers
            # shift, so we track the cumulative offset.
            offset = 0
            for error_line in error_lines:
                adjusted_line = error_line + offset
                decl_start = find_declaration_start(lines, adjusted_line)

                # Check which options are already present
                present = options_present_at(lines, decl_start)
                missing = [opt for opt in options if opt not in present]
                if not missing:
                    already_present += 1
                    continue

                # Try each candidate combination of missing options
                succeeded = False
                last_output = output
                for combo in candidates(missing):
                    insert = [set_option_line(opt) for opt in combo]
                    new_lines = lines[:decl_start] + insert + lines[decl_start:]
                    filepath.write_text("".join(new_lines))
                    ok, build_output = traverser.lake_build(module_name, PROJECT_DIR, timeout)
                    last_output = build_output

                    if ok:
                        lines = new_lines
                        offset += len(combo)
                        fixed += 1
                        _set_last(combo)
                        succeeded = True
                        return FileResult(fixed=fixed, already_present=already_present)

                    # Check if this specific error is gone
                    new_errors = parse_errors_in_file(build_output, rel_path)
                    shifted = adjusted_line + len(combo)
                    if shifted not in new_errors:
                        lines = new_lines
                        offset += len(combo)
                        fixed += 1
                        _set_last(combo)
                        succeeded = True
                        break

                    # Revert this attempt
                    filepath.write_text("".join(lines))

                if not succeeded:
                    raise UnfixableError(
                        f"no option combination fixed error at line {error_line}",
                        last_output,
                    )

        except UnfixableError:
            raise
        except BaseException:
            filepath.write_text(original_text)
            raise
        finally:
            traverser.inflight_unregister(filepath)

        return FileResult(fixed=fixed, already_present=already_present)

    return process_module


def print_summary(
    results: list[TraversalResult],
    dag: DAG,
    duration: float,
):
    total_fixed = 0
    files_fixed = 0
    files_failed = 0

    for tr in results:
        if tr.error:
            files_failed += 1
        elif tr.result and tr.result.fixed > 0:
            files_fixed += 1
            total_fixed += tr.result.fixed

    skipped = len(dag.modules) - len(results)

    print()
    print("=" * 60)
    print("SUMMARY")
    print("=" * 60)
    print(f"  Modules processed:  {len(results)}")
    print(f"  Modules fixed:      {files_fixed}")
    print(f"  Modules failed:     {files_failed}")
    print(f"  Modules skipped:    {skipped}")
    print(f"  set_options added:  {total_fixed}")
    print(f"  Duration:           {duration:.0f}s")

    if files_failed:
        print()
        print("Failed modules:")
        for tr in results:
            if tr.error:
                print(f"  {tr.module_name}: {tr.error}")
                if isinstance(tr.error, UnfixableError) and tr.error.output.strip():
                    for line in tr.error.output.strip().splitlines()[-10:]:
                        print(f"    {line}")

    if skipped:
        processed = {tr.module_name for tr in results}
        skipped_names = sorted(set(dag.modules.keys()) - processed)
        print(f"\nSkipped modules ({skipped}):")
        for name in skipped_names[:20]:
            print(f"  {name}")
        if len(skipped_names) > 20:
            print(f"  ... and {len(skipped_names) - 20} more")


def main():
    parser = argparse.ArgumentParser(
        description="Add set_option ... false in before failing declarations."
    )
    parser.add_argument(
        "--option",
        help="Only use this specific option (default: try all known options)",
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
        help="Skip the initial build (build every module individually)",
    )
    parser.add_argument(
        "--open",
        action="store_true",
        help="Open files that failed to fix in the default editor",
    )
    args = parser.parse_args()

    options = [args.option] if args.option else DEFAULT_OPTIONS

    start_time = time.time()

    # Build DAG
    print("Building import DAG...", flush=True)
    dag = DAG.from_directories(PROJECT_DIR)
    print(f"  {len(dag.modules)} modules parsed")

    # Filter to requested files
    if args.files:
        requested = set()
        for f in args.files:
            mod = f.replace("/", ".").removesuffix(".lean")
            requested.add(mod)
        dag = dag.subset(requested)
        print(f"  Filtered to {len(dag.modules)} modules")

    # Initial build: run a full build to find which modules have errors,
    # then skip everything outside their forward cone in the DAG.
    skip: set[str] | None = None
    if not args.no_initial and not args.files:
        error_mods, build_output = initial_build()
        if not error_mods:
            print("No errors found, nothing to do.")
            return
        cone = dag.forward_cone(error_mods)
        skip = set(dag.modules.keys()) - cone
        print(f"  {len(cone)} modules in forward cone, skipping {len(skip)}")

    # Weight = LOC × error count, so expensive files get critical-path
    # priority in the DAG traversal scheduler.
    weights: dict[str, int] | None = None
    if not args.no_initial and not args.files:
        error_counts = count_errors_per_module(build_output)
        weights = {}
        for name in error_counts:
            if name in dag.modules:
                fp = dag.project_root / dag.modules[name].filepath
                weights[name] = len(fp.read_text().splitlines()) * error_counts[name]

    # Traverse forward
    traverser = DAGTraverser()
    display = _AddDisplay(dag, open_on_failure=args.open)
    action = make_process_module(options, args.timeout, traverser)

    display.start(len(dag.modules))
    try:
        results = traverser.traverse(
            dag,
            action,
            direction="forward",
            max_workers=args.max_workers,
            progress_callback=display.on_progress,
            module_callback=display.on_module,
            stop_on_failure=True,
            skip=skip,
            weights=weights,
        )
    except KeyboardInterrupt:
        display.stop()
        print("\nInterrupted. Press Ctrl-C again if the process doesn't exit.", flush=True)
        traverser.force_exit(1)
    finally:
        display.stop()

    duration = time.time() - start_time
    print_summary(results, dag, duration)

    failed = any(tr.error for tr in results)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
