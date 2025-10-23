#!/usr/bin/env python3
"""
Wrapper script for `lake build` to be used in GitHub actions that:
1. Groups only normal build output (✔ lines) into collapsible log groups
2. Emits all non-✔ lines (including ℹ/⚠/✖ and summaries) outside groups
3. Extracts infos/warnings/errors to JSON for step outputs without altering the stream

Written to GITHUB_OUTPUT:
- `warning_count`, `error_count`, `info_count`: integers counting the number of warnings, errors and
  info / trace messages.
- `summary`: full summary JSON described below.

Summary JSON format:
- Top-level object with keys:
  - warnings: list of issue objects (warning blocks)
  - errors: list of issue objects (error blocks)
  - infos: list of issue objects (info blocks)
  - warning_count: integer
  - error_count: integer
  - info_count: integer

- Each issue object contains:
  - file_info: object with parsed progress/target info, if available
    - current: integer (N in "[N/M]")
    - total: integer (M in "[N/M]")
    - target: string (module/target token from the log)
    - file: string or null (converted Lean filename; null for non-file targets containing ':')
  - messages: list of strings (subset of lines in the block that include typical markers like "warning:", "error:", or "info:")
  - full_output: string (the entire contiguous block captured for the issue)

State machine overview:
- States
  - OUTSIDE: No open group; not collecting an issue.
  - GROUP_OPEN: A ::group:: is open; only ✔ lines are printed inside the group.
  - IN_WARNING: Collecting a warning block (⚠ line + following lines).
  - IN_ERROR: Collecting an error block (✖ line + following lines).
  - IN_INFO: Collecting an info block (ℹ line + following lines).

- Events (derived per line)
  - NORMAL: Line starts with ✔
  - NEW_WARNING: Line starts with ⚠
  - NEW_ERROR: Line starts with ✖
  - NEW_INFO: Line starts with ℹ
  - OTHER: Any other line (including end-of-build summary lines)

- Transitions (action → next state)
  - OUTSIDE + NORMAL → open_group; print → GROUP_OPEN
  - OUTSIDE + NEW_* → start_issue; print → IN_*
  - OUTSIDE + OTHER → print → OUTSIDE
  - GROUP_OPEN + NORMAL → print → GROUP_OPEN
  - GROUP_OPEN + NEW_*/OTHER → close_group; print; (start_issue if NEW_*) → IN_* or OUTSIDE
  - IN_* + NORMAL → flush_issue; open_group; print → GROUP_OPEN
  - IN_* + NEW_* → flush_issue; start_issue; print → IN_*
  - IN_* + OTHER → if summary-line then flush_issue else append_issue; print → OUTSIDE or IN_*
  - EOF → flush_issue; close_group

Relevant parts of `lake`:
- `lake build`'s log output is generated [here](https://github.com/leanprover/lean4/blob/59573646c227d940962c08a1e77ce51177a024ea/src/lake/Lake/Build/Run.lean#L132)
- icons (other than ✔) are defined [here](https://github.com/leanprover/lean4/blob/59573646c227d940962c08a1e77ce51177a024ea/src/lake/Lake/Util/Log.lean#L87)
"""

import sys
import subprocess
import re
import json
from typing import Dict, Any
from enum import Enum, auto

class BuildOutputProcessor:
    def __init__(self):
        self.warnings = []
        self.errors = []
        self.infos = []
        self.current_issue = []
        self.group_open = False
        class _State(Enum):
            OUTSIDE = auto()
            GROUP_OPEN = auto()
            IN_WARNING = auto()
            IN_ERROR = auto()
            IN_INFO = auto()
        self.State = _State
        self.state = self.State.OUTSIDE
        class _Evt(Enum):
            NORMAL = auto()
            NEW_WARNING = auto()
            NEW_ERROR = auto()
            NEW_INFO = auto()
            OTHER = auto()
        self.Evt = _Evt

    def start_group(self, name: str):
        """Start a GitHub Actions log group"""
        print(f"::group::{name}", flush=True)

    def end_group(self):
        """End a GitHub Actions log group"""
        print("::endgroup::", flush=True)

    def close_group_if_open(self):
        """Close the current group if one is open."""
        if self.group_open:
            self.end_group()
            self.group_open = False

    def open_group_for_line(self, line: str):
        """Open a group named by progress info from this line, if not already open."""
        if not self.group_open:
            stripped = line.strip()
            first_match = re.search(r'\[(\d+)/(\d+)\]', stripped)
            if first_match:
                group_name = f"Build progress [starting at {first_match.group(1)}/{first_match.group(2)}]"
            else:
                group_name = "Build progress"
            self.start_group(group_name)
            self.group_open = True

    def is_normal_line(self, line: str) -> bool:
        """Check if line is normal build output (checkmark)."""
        return line.strip().startswith('✔')

    def is_warning_start(self, line: str) -> bool:
        """Check if line starts a warning"""
        return line.strip().startswith('⚠')

    def is_error_start(self, line: str) -> bool:
        """Check if line starts an error"""
        return line.strip().startswith('✖')

    def is_info_start(self, line: str) -> bool:
        """Check if line starts an info block"""
        return line.strip().startswith('ℹ')

    def is_build_summary(self, line: str) -> bool:
        """Check if line is a build summary (end of build output)"""
        stripped = line.strip()
        return (stripped.startswith('error: build failed') or
                stripped.startswith('Build completed successfully') or
                stripped.startswith('Some required targets logged failures:') or
                stripped.startswith('Error: Process completed with exit code'))

    def extract_file_info(self, line: str) -> Dict[str, Any]:
        """Extract progress and target info from a build line.

        Matches: "[N/M] <verb> <target>" where <verb> is any non-space token and
        <target> is captured as a build target/module name.

        Converts module-like targets to a Lean filename by replacing '.' with '/'
        and appending ".lean" (e.g. Mathlib.Analysis.Foo → Mathlib/Analysis/Foo.lean).
        If the target contains a colon (e.g. batteries:extraDep), it is treated
        as a non-file target and no filename is generated.
        """
        match = re.search(r'\[(\d+)/(\d+)\]\s+(\S+)\s+([^\s]+)', line)
        if not match:
            return {}

        target = match.group(4)
        # Non-file targets contain a colon (e.g., "batteries:extraDep").
        if ':' in target:
            file_path = None
        else:
            # Single regex replacement: dots → slashes, then append .lean
            file_path = re.sub(r'\.', '/', target) + '.lean'

        return {
            'current': int(match.group(1)),
            'total': int(match.group(2)),
            'target': target,
            'file': file_path,
        }

    def process_line(self, line: str):
        """Process a single line of output via an explicit FSM, streaming output immediately."""

        # Classify input line into an event
        if self.is_warning_start(line):
            evt = self.Evt.NEW_WARNING
        elif self.is_error_start(line):
            evt = self.Evt.NEW_ERROR
        elif self.is_info_start(line):
            evt = self.Evt.NEW_INFO
        elif self.is_normal_line(line):
            evt = self.Evt.NORMAL
        else:
            evt = self.Evt.OTHER

        # State-driven behavior
        if self.state == self.State.OUTSIDE:
            if evt == self.Evt.NORMAL:
                self.open_group_for_line(line)
                print(line, end='', flush=True)
                self.state = self.State.GROUP_OPEN
            elif evt == self.Evt.NEW_WARNING:
                self.current_issue = [line]
                print(line, end='', flush=True)
                self.state = self.State.IN_WARNING
            elif evt == self.Evt.NEW_ERROR:
                self.current_issue = [line]
                print(line, end='', flush=True)
                self.state = self.State.IN_ERROR
            elif evt == self.Evt.NEW_INFO:
                self.current_issue = [line]
                print(line, end='', flush=True)
                self.state = self.State.IN_INFO
            elif evt == self.Evt.OTHER:
                # Print outside any groups
                self.close_group_if_open()
                print(line, end='', flush=True)
            return

        if self.state == self.State.GROUP_OPEN:
            if evt == self.Evt.NORMAL:
                print(line, end='', flush=True)
            else:
                # Close group, then handle the event outside the group
                self.close_group_if_open()
                if evt == self.Evt.NEW_WARNING:
                    self.current_issue = [line]
                    print(line, end='', flush=True)
                    self.state = self.State.IN_WARNING
                elif evt == self.Evt.NEW_ERROR:
                    self.current_issue = [line]
                    print(line, end='', flush=True)
                    self.state = self.State.IN_ERROR
                elif evt == self.Evt.NEW_INFO:
                    self.current_issue = [line]
                    print(line, end='', flush=True)
                    self.state = self.State.IN_INFO
                else:
                    print(line, end='', flush=True)
                    self.state = self.State.OUTSIDE
            return

        if self.state in (self.State.IN_WARNING, self.State.IN_ERROR, self.State.IN_INFO):
            if evt == self.Evt.NORMAL:
                self.flush_issue()
                self.open_group_for_line(line)
                print(line, end='', flush=True)
                self.state = self.State.GROUP_OPEN
            elif evt == self.Evt.NEW_WARNING:
                self.flush_issue()
                self.current_issue = [line]
                print(line, end='', flush=True)
                self.state = self.State.IN_WARNING
            elif evt == self.Evt.NEW_ERROR:
                self.flush_issue()
                self.current_issue = [line]
                print(line, end='', flush=True)
                self.state = self.State.IN_ERROR
            elif evt == self.Evt.NEW_INFO:
                self.flush_issue()
                self.current_issue = [line]
                print(line, end='', flush=True)
                self.state = self.State.IN_INFO
            else:  # OTHER → continuation or summary
                if self.is_build_summary(line):
                    self.flush_issue()
                    print(line, end='', flush=True)
                    self.state = self.State.OUTSIDE
                else:
                    self.current_issue.append(line)
                    print(line, end='', flush=True)
            return

    def flush_issue(self):
        """Record the current warning/error block for the summary."""
        if not self.current_issue:
            return

        issue_text = ''.join(self.current_issue)
        file_info = self.extract_file_info(self.current_issue[0])

        # Extract actual info/warning/error messages
        messages = []
        for line in self.current_issue:
            low = line.lower()
            if 'warning:' in low or 'error:' in low or 'info:' in low or 'trace:' in low:
                messages.append(line.strip())

        issue_data = {
            'file_info': file_info,
            'messages': messages,
            'full_output': issue_text
        }

        if self.state == self.State.IN_WARNING:
            self.warnings.append(issue_data)
        elif self.state == self.State.IN_ERROR:
            self.errors.append(issue_data)
        elif self.state == self.State.IN_INFO:
            self.infos.append(issue_data)

        # Do not print here; lines were already streamed as they arrived.
        self.current_issue = []
        self.state = self.State.OUTSIDE

    def finalize(self):
        """Finalize processing"""
        self.flush_issue()
        self.close_group_if_open()

    def get_summary(self) -> Dict[str, Any]:
        """Get summary of warnings and errors"""
        return {
            'warnings': self.warnings,
            'errors': self.errors,
            'infos': self.infos,
            'warning_count': len(self.warnings),
            'error_count': len(self.errors),
            'info_count': len(self.infos),
        }

def main():
    if len(sys.argv) < 2:
        print("Usage: wrapper.py <command> [args...]", file=sys.stderr)
        sys.exit(1)

    import os
    processor = BuildOutputProcessor()

    # Run the command and process output line by line
    process = subprocess.Popen(
        sys.argv[1:],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1
    )

    try:
        if process.stdout is not None:
            for line in process.stdout:
                processor.process_line(line)
        else:
            print("Process did not produce any stdout or an error occurred.")
            if process.stderr:
                print("Stderr:", process.stderr)

        process.wait()
        processor.finalize()

        # Get summary and output as JSON string for step output
        summary = processor.get_summary()
        summary_json = json.dumps(summary)

        # Set GitHub Actions outputs using GITHUB_OUTPUT
        github_output = os.environ.get('GITHUB_OUTPUT')
        if github_output:
            with open(github_output, 'a') as f:
                f.write(f"warning_count={summary['warning_count']}\n")
                f.write(f"error_count={summary['error_count']}\n")
                f.write(f"info_count={summary['info_count']}\n")
                # For multiline output, use delimiter syntax
                f.write(f"summary<<EOF\n{summary_json}\nEOF\n")
        else:
            print("Warning: GITHUB_OUTPUT environment variable not set", file=sys.stderr)
            print(f"warning_count={summary['warning_count']}", file=sys.stderr)
            print(f"error_count={summary['error_count']}", file=sys.stderr)
            print(f"info_count={summary['info_count']}", file=sys.stderr)
            print(f"summary={summary_json}", file=sys.stderr)

        # Exit with the same code as the subprocess
        sys.exit(process.returncode)

    except KeyboardInterrupt:
        process.terminate()
        sys.exit(130)

if __name__ == "__main__":
    main()
