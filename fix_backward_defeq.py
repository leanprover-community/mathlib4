#!/usr/bin/env python3
"""
Script to automatically add `set_option backward.isDefEq.respectTransparency false in`
before declarations with errors, testing if it fixes the error.
"""

import subprocess
import re
import os
import sys
from abc import ABC, abstractmethod
from pathlib import Path
from threading import Lock, Thread
from queue import Queue, Empty
import time

PROJECT_DIR = Path(__file__).parent

# ANSI escape codes
CLEAR_LINE = "\033[2K"
HIDE_CURSOR = "\033[?25l"
SHOW_CURSOR = "\033[?25h"


class FixStrategy(ABC):
    """Abstract strategy for proposing and verifying fixes for build errors."""

    @abstractmethod
    def propose_fix(self, filepath: str, lines: list[str], error_line: int
                    ) -> tuple[list[str] | None, str]:
        """Propose a fix for the error at error_line.

        Returns (new_lines, message).
        - new_lines not None: the fix to try, message describes it
        - new_lines is None: can't fix, message explains why
        """

    @abstractmethod
    def did_fix_work(self, filepath: str, error_line: int,
                     new_errors: dict[str, list[int]]) -> tuple[bool, str]:
        """Check if the fix resolved the error.

        Returns (success, message).
        """


class BackwardDefEqStrategy(FixStrategy):
    """Fix errors by adding `set_option backward.isDefEq.respectTransparency false in`."""

    SET_OPTION_LINE = "set_option backward.isDefEq.respectTransparency false in"

    def _is_inside_block_comment(self, lines: list[str], line_idx: int) -> bool:
        """Check if the given line index is inside a /- ... -/ block comment (including /-- and /-!)."""
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

    def _find_declaration_start(self, lines: list[str], error_line: int) -> int:
        """Find the start of the declaration containing the error."""
        idx = error_line - 1

        while idx > 0:
            idx -= 1
            if lines[idx].strip() == "":
                if not self._is_inside_block_comment(lines, idx):
                    return idx + 1

        return 0

    def propose_fix(self, filepath: str, lines: list[str], error_line: int
                    ) -> tuple[list[str] | None, str]:
        decl_start = self._find_declaration_start(lines, error_line)

        # Check if set_option is already there
        if decl_start > 0 and self.SET_OPTION_LINE in lines[decl_start - 1]:
            return None, f"set_option already present at line {decl_start}"

        if lines[decl_start].strip().startswith(self.SET_OPTION_LINE):
            return None, "set_option already at declaration start"

        # Insert the set_option line
        new_lines = lines[:decl_start] + [self.SET_OPTION_LINE + "\n"] + lines[decl_start:]
        return new_lines, f"inserted set_option before line {decl_start + 1}"

    def did_fix_work(self, filepath: str, error_line: int,
                     new_errors: dict[str, list[int]]) -> tuple[bool, str]:
        expected_error_line = error_line + 1
        if filepath in new_errors and expected_error_line in new_errors[filepath]:
            return False, f"set_option didn't fix error at line {error_line}"
        return True, ""


class StatusDisplay:
    """Manages a multi-line status display that updates in place."""

    def __init__(self, num_workers: int):
        self.num_workers = num_workers
        self.lock = Lock()
        self.worker_status: dict[int, str] = {i: "idle" for i in range(num_workers)}
        self.summary_line = ""
        self.build_status = ""  # e.g. "3000/7000 built successfully"
        self.discovery_status = ""
        self.last_failed = ""  # Last file we gave up on
        self.messages: list[str] = []  # Messages to print above status
        self.displayed_lines = 0
        self.started = False

    def start(self):
        """Initialize the display."""
        self.started = True
        print(HIDE_CURSOR, end="", flush=True)
        self._redraw()

    def stop(self):
        """Clean up the display."""
        if self.started:
            print(SHOW_CURSOR, end="", flush=True)
            self.started = False

    def _redraw(self):
        """Redraw the entire status display."""
        if not self.started:
            return

        # Move cursor up to overwrite previous status display (not messages)
        if self.displayed_lines > 0:
            print(f"\033[{self.displayed_lines}A", end="")

        # Print any queued messages first (these scroll up and are not overwritten)
        for msg in self.messages:
            print(CLEAR_LINE + msg)
        self.messages.clear()

        # Build status lines (these get overwritten each time)
        status_lines = []

        # Summary line
        status_lines.append(CLEAR_LINE + self.summary_line)

        # Build success status
        if self.build_status:
            status_lines.append(CLEAR_LINE + f"  🏗️  {self.build_status}")
        else:
            status_lines.append(CLEAR_LINE)

        # Discovery build status (always show line for consistent height)
        if self.discovery_status:
            status_lines.append(CLEAR_LINE + f"  🔍 {self.discovery_status}")
        else:
            status_lines.append(CLEAR_LINE)

        # Last failed file (clickable path)
        if self.last_failed:
            status_lines.append(CLEAR_LINE + f"  ❌ {self.last_failed}")
        else:
            status_lines.append(CLEAR_LINE)

        # Worker status lines
        for i in range(self.num_workers):
            status = self.worker_status.get(i, "idle")
            status_lines.append(CLEAR_LINE + f"  [{i}] {status}")

        # Print status lines
        output = "\n".join(status_lines)
        print(output, flush=True)
        self.displayed_lines = len(status_lines)

    def set_summary(self, text: str):
        """Update the summary line."""
        with self.lock:
            self.summary_line = text
            self._redraw()

    def set_worker_status(self, worker_id: int, status: str):
        """Update a worker's status."""
        with self.lock:
            self.worker_status[worker_id] = status
            self._redraw()

    def set_discovery_status(self, status: str):
        """Update the discovery build status."""
        with self.lock:
            self.discovery_status = status
            self._redraw()

    def set_build_status(self, status: str):
        """Update the build success status."""
        with self.lock:
            self.build_status = status
            self._redraw()

    def set_last_failed(self, filepath: str, reason: str):
        """Update the last failed file display."""
        with self.lock:
            self.last_failed = f"{filepath}  ({reason})"
            self._redraw()

    def log_message(self, msg: str):
        """Log a message that scrolls up above the status display."""
        with self.lock:
            self.messages.append(msg)
            self._redraw()


class BuildCoordinator:
    """Coordinates parallel file processing with dynamic discovery of new failing files."""

    def __init__(self, strategy: FixStrategy, num_workers: int):
        self.strategy = strategy
        self.num_workers = num_workers
        self.work_queue: Queue[str] = Queue()
        self.display = StatusDisplay(num_workers)

        # File tracking (all protected by lock)
        self.lock = Lock()
        self.queued_files: set[str] = set()      # Files in queue or being processed
        self.processed_files: set[str] = set()   # Files we've finished with
        self.in_progress: set[str] = set()       # Files currently being worked on
        self.failed_files: dict[str, str] = {}   # filepath -> reason

        # Statistics
        self.total_fixes = 0
        self.build_count = 0

        # Discovery build control
        self.discovery_build_running = False
        self.discovery_build_pending = False

        # Control
        self.shutdown = False

    def log(self, msg: str):
        """Log a message (scrolls above status display when running)."""
        if self.display.started:
            self.display.log_message(msg)
        else:
            print(msg, flush=True)

    def update_summary(self):
        """Update the summary line with current stats."""
        with self.lock:
            queued = self.work_queue.qsize()
            in_prog = len(self.in_progress)
            done = len(self.processed_files)
            fixes = self.total_fixes
        self.display.set_summary(
            f"📊 Queued: {queued} | In progress: {in_prog} | Done: {done} | Fixes: {fixes}"
        )

    def run_lake_build(self, on_output=None, nice=False) -> str:
        """Run lake build and capture output. Optionally calls on_output(line) for each line."""
        cmd = ["lake", "build", "Mathlib", "MathlibTest", "Archive", "Counterexamples", "--verbose"]
        if nice:
            cmd = ["nice"] + cmd
        proc = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            cwd=PROJECT_DIR
        )
        output_lines = []
        for line in proc.stdout:
            output_lines.append(line)
            if on_output:
                on_output(line)
        proc.wait()
        return "".join(output_lines)

    def run_lake_build_file(self, filepath: str) -> str:
        """Run lake build on a specific file and capture output."""
        rel_path = filepath
        if rel_path.startswith("./"):
            rel_path = rel_path[2:]
        if rel_path.endswith(".lean"):
            rel_path = rel_path[:-5]
        module_name = rel_path.replace("/", ".")

        result = subprocess.run(
            ["lake", "build", module_name],
            capture_output=True,
            text=True,
            cwd=PROJECT_DIR
        )
        return result.stdout + result.stderr

    def parse_build_stats(self, build_output: str) -> dict:
        """Parse lake build output for summary statistics."""
        # Get total from [N/M] pattern
        build_pattern = re.compile(r'\[(\d+)/(\d+)\]')
        total_files = 0
        for match in build_pattern.finditer(build_output):
            total_files = max(total_files, int(match.group(2)))

        # Count by marker type (with --verbose, all files are printed)
        built_pattern = re.compile(r'✔ \[\d+/\d+\]')
        fail_pattern = re.compile(r'✖ \[\d+/\d+\]')

        built = len(built_pattern.findall(build_output))
        failed = len(fail_pattern.findall(build_output))

        return {
            "total": total_files,
            "success": built,
            "failed": failed,
        }

    def parse_errors(self, build_output: str) -> dict[str, list[int]]:
        """Parse lake build output to find files with errors and their line numbers."""
        error_pattern = re.compile(r'^error: ([^:\s]+\.lean):(\d+):\d+:', re.MULTILINE)
        files_with_errors: dict[str, list[int]] = {}

        for match in error_pattern.finditer(build_output):
            filepath = match.group(1)
            line_num = int(match.group(2))

            if filepath not in files_with_errors:
                files_with_errors[filepath] = []
            if line_num not in files_with_errors[filepath]:
                files_with_errors[filepath].append(line_num)

        for filepath in files_with_errors:
            files_with_errors[filepath].sort()

        return files_with_errors

    def add_files_to_queue(self, files: list[str]) -> int:
        """Add files to queue if not already queued/processed. Returns count added."""
        added = 0
        with self.lock:
            for f in files:
                if f not in self.queued_files and f not in self.processed_files:
                    self.queued_files.add(f)
                    self.work_queue.put(f)
                    added += 1
        return added

    def request_discovery_build(self):
        """Request a discovery build. Only one runs at a time; extra requests are coalesced."""
        with self.lock:
            if self.discovery_build_running:
                # A build is running; mark that another is needed when it finishes
                self.discovery_build_pending = True
                return
            self.discovery_build_running = True

        # Run builds until no more are pending
        while True:
            self._run_discovery_build()

            with self.lock:
                if self.discovery_build_pending:
                    self.discovery_build_pending = False
                    # Continue loop to run another build
                else:
                    self.discovery_build_running = False
                    self.display.set_discovery_status("")
                    break

    def _run_discovery_build(self):
        """Actually run a discovery build (internal, called by request_discovery_build)."""
        with self.lock:
            self.build_count += 1
            build_num = self.build_count

        progress_re = re.compile(r'\[(\d+)/(\d+)\]')

        def update_progress(line):
            m = progress_re.search(line)
            if m:
                self.display.set_discovery_status(
                    f"Build #{build_num} [{m.group(1)}/{m.group(2)}]")

        self.display.set_discovery_status(f"Build #{build_num} running...")
        build_output = self.run_lake_build(on_output=update_progress, nice=True)

        log_file = f"/tmp/lake-build-discovery-{build_num}.log"
        with open(log_file, "w") as f:
            f.write(build_output)

        stats = self.parse_build_stats(build_output)
        files_with_errors = self.parse_errors(build_output)

        new_files = [f for f in files_with_errors.keys()
                     if f not in self.queued_files and f not in self.processed_files]
        added = self.add_files_to_queue(new_files)

        self.update_summary()
        self.display.set_build_status(f"{stats['success']}/{stats['total']} built successfully")
        self.display.set_discovery_status(f"Build #{build_num}: +{added} files")

        if added > 0:
            self.log(f"🔍 Discovery #{build_num}: found {added} new files")

    def process_file(self, filepath: str, worker_id: int) -> tuple[int, int]:
        """
        Process a single file, trying to fix errors using the strategy.
        Returns (fixes_applied, errors_remaining).
        """
        def status(msg: str):
            self.display.set_worker_status(worker_id, f"{filepath}: {msg}")

        status("starting...")

        if not os.path.exists(filepath):
            self.log(f"✗ File not found: {filepath}")
            return (0, 0)

        fixes_applied = 0

        # Initial build to get errors
        status("building...")
        build_output = self.run_lake_build_file(filepath)
        errors = self.parse_errors(build_output)

        initial_error_count = len(errors.get(filepath, []))

        while filepath in errors and errors[filepath]:
            error_lines = errors[filepath]
            first_error_line = error_lines[0]
            progress = f"line {first_error_line}, fixed {fixes_applied}/{initial_error_count}"

            status(progress)

            with open(filepath, 'r') as f:
                lines = f.readlines()

            new_lines, message = self.strategy.propose_fix(filepath, lines, first_error_line)

            if new_lines is None:
                status(f"⚠ {message}")
                with self.lock:
                    self.failed_files[filepath] = message
                self.display.set_last_failed(filepath, message)
                break

            with open(filepath, 'w') as f:
                f.writelines(new_lines)

            # Rebuild and check - reuse this output for next iteration
            status(f"{progress}, testing...")
            build_output = self.run_lake_build_file(filepath)
            errors = self.parse_errors(build_output)

            success, reason = self.strategy.did_fix_work(filepath, first_error_line, errors)

            if not success:
                status(f"{progress}, reverting...")
                with open(filepath, 'w') as f:
                    f.writelines(lines)
                with self.lock:
                    self.failed_files[filepath] = reason
                self.display.set_last_failed(filepath, reason)
                break
            else:
                fixes_applied += 1
                self.log(f"✓ {filepath}:{first_error_line} fixed!")
                # errors dict is already updated from the test build, loop continues

        status("done")
        errors_remaining = len(errors.get(filepath, []))
        return (fixes_applied, errors_remaining)

    def worker(self, worker_id: int):
        """Worker thread that processes files from the queue."""
        self.display.set_worker_status(worker_id, "idle")

        while not self.shutdown:
            try:
                filepath = self.work_queue.get(timeout=1.0)
            except Empty:
                self.display.set_worker_status(worker_id, "idle")
                continue

            with self.lock:
                if filepath in self.processed_files:
                    self.work_queue.task_done()
                    continue
                self.in_progress.add(filepath)

            self.update_summary()

            try:
                fixes, remaining = self.process_file(filepath, worker_id)

                with self.lock:
                    self.in_progress.discard(filepath)
                    self.processed_files.add(filepath)
                    self.total_fixes += fixes

                self.update_summary()

                if fixes > 0:
                    self.log(f"✓ {filepath}: {fixes} fixes applied")
                elif remaining > 0:
                    self.log(f"⚠ {filepath}: {remaining} errors remain")
                else:
                    self.log(f"○ {filepath}: no changes needed")

                self.display.set_worker_status(worker_id, "idle")

                # If we applied fixes, trigger a discovery build
                if fixes > 0:
                    Thread(target=self.request_discovery_build, daemon=True).start()

            except Exception as e:
                self.log(f"✗ {filepath}: {e}")
                with self.lock:
                    self.in_progress.discard(filepath)
                    self.processed_files.add(filepath)
                    self.failed_files[filepath] = f"Exception: {e}"
                self.display.set_worker_status(worker_id, "idle")
                self.update_summary()

            self.work_queue.task_done()

    def run(self):
        """Main entry point."""
        print("=" * 60)
        print("Running initial lake build to find all errors...")
        print("=" * 60)

        progress_re = re.compile(r'\[(\d+)/(\d+)\]')

        def show_progress(line):
            m = progress_re.search(line)
            if m:
                print(f"\r  Building... [{m.group(1)}/{m.group(2)}]", end="", flush=True)

        build_output = self.run_lake_build(on_output=show_progress)
        print()  # newline after progress

        with open("/tmp/lake-build-initial.log", "w") as f:
            f.write(build_output)
        print("Build output saved to /tmp/lake-build-initial.log")

        stats = self.parse_build_stats(build_output)
        files_with_errors = self.parse_errors(build_output)

        print(f"\nBuild summary:")
        print(f"  Total files:       {stats['total']}")
        print(f"  Succeeded:         {stats['success']}")
        print(f"  Failed:            {stats['failed']}")
        print(f"  Files with errors: {len(files_with_errors)}")

        if not files_with_errors:
            print("\nNo errors found!")
            return

        self.add_files_to_queue(list(files_with_errors.keys()))

        print(f"\nStarting {self.num_workers} workers...\n")

        # Start the display
        self.display.start()
        self.update_summary()
        self.display.set_build_status(f"{stats['success']}/{stats['total']} built successfully")

        try:
            # Start workers
            for i in range(self.num_workers):
                Thread(target=self.worker, args=(i,), daemon=True).start()

            # Wait for queue to drain and all work to complete.
            # We must also wait for any discovery builds, since they may
            # find new failing files to add to the queue.
            while True:
                with self.lock:
                    active = len(self.in_progress)
                    queued = self.work_queue.qsize()
                    discovering = self.discovery_build_running or self.discovery_build_pending

                if active == 0 and queued == 0 and not discovering:
                    # Double-check after a brief pause
                    time.sleep(0.5)
                    with self.lock:
                        if (len(self.in_progress) == 0
                                and self.work_queue.qsize() == 0
                                and not self.discovery_build_running
                                and not self.discovery_build_pending):
                            break

                time.sleep(0.5)

            self.shutdown = True

        finally:
            self.display.stop()

        # Final summary
        print("\n" + "=" * 60)
        print("FINAL SUMMARY")
        print("=" * 60)

        print(f"\nTotal fixes applied: {self.total_fixes}")
        print(f"Files processed: {len(self.processed_files)}")
        print(f"Discovery builds: {self.build_count}")

        if self.failed_files:
            print("\n" + "=" * 60)
            print("FILES THAT NEED MANUAL ATTENTION")
            print("=" * 60)
            for filepath, reason in sorted(self.failed_files.items()):
                print(f"  {filepath}")
                print(f"    Reason: {reason}")


def main():
    num_workers = os.cpu_count() or 4
    strategy = BackwardDefEqStrategy()
    coordinator = BuildCoordinator(strategy, num_workers)

    try:
        coordinator.run()
    except KeyboardInterrupt:
        coordinator.display.stop()
        print("\n\nInterrupted by user")
        sys.exit(1)


if __name__ == "__main__":
    main()
