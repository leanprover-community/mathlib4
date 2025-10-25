#!/usr/bin/env python3
"""
Usage: lake-build-wrapper.py <output_file.json> <command> [args...]

Wrapper script for `lake build` to be used in GitHub actions that:
1. Groups normal build output (✔ lines) into collapsible log groups
2. Also groups ℹ/⚠/✖ blocks into collapsible log groups; build summaries remain outside groups
3. Extracts information about infos/warnings/errors to JSON output file

Example `lake build` log output:
```
✔ [4000/9999] Built Mathlib.NumberTheory.LSeries.PrimesInAP
✖ [5000/9999] Building MathlibTest.toAdditive (4.2s)
trace: .> LEAN_PATH=...
Error: error: MathlibTest/toAdditive.lean:168:105: Fields missing: `fileName`, `fileMap`
Error: error: MathlibTest/toAdditive.lean:219:60: invalid {...} notation, structure type expected
  Name
error: Lean exited with code 1
✔ [6000/9999] Built MathlibTest.MathlibTestExecutable (3.2s)
✔ [7000/9999] Built Mathlib.Analysis.CStarAlgebra.Module.Defs
⚠ [8000/9999] Built Mathlib.Algebra.Quandle (7.0s)
warning: Mathlib/Algebra/Quandle.lean:122:0: This line exceeds the 100 character limit, please shorten it!

Note: This linter can be disabled with `set_option linter.style.longLine false`
✔ [9999/9999] Built Mathlib (111s)
Build completed successfully (7401 jobs).
```

Notes:
- a line beginning with ✔ is a "normal line" and contiguous sequences of these will be collapsed into log groups
- build lines beginning with ℹ/⚠/✖ begin info/warning/error blocks; these blocks are grouped as well
- the title of each ℹ/⚠/✖ group is exactly the starting line; that starting line is not echoed again inside the group body
- blocks are ended by either a normal line ✔ or a build summary line like "Build completed" / "Some required targets logged failures:"
- in the example above, there is one error block and one warning block
- note that there can be more than one error or warning in a block

Summary JSON format:
- Top-level object with keys:
  - warnings: list of block objects (see below)
  - errors: list of block objects
  - infos: list of block objects
  - warning_count: integer (count of warning blocks)
  - error_count: integer (count of error blocks)
  - info_count: integer (count of info blocks)

- Each block object contains:
  - file_info: object with parsed progress/target info, if available
    - current: integer (N in "[N/M]")
    - total: integer (M in "[N/M]")
    - target: string (module/target token from the log,
      e.g. `Mathlib.Analysis.CStarAlgebra.Module.Defs` or `batteries:extraDep`)
    - file: string or null (converted Lean filename,
      e.g. `Mathlib/Analysis/CStarAlgebra/Module/Defs.lean`;
      null for non-file targets containing ':')
  - messages: list of strings (subset of lines in the block that include typical markers like "warning:", "error:", or "info:")
  - full_output: string (the entire contiguous block)

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
        self.current_block = []
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
        """Open a progress group named by this line's [N/M] info.

        Precondition: no group is currently open (caller closed it if necessary).
        """
        stripped = line.strip()
        first_match = re.search(r'\[(\d+)/(\d+)\]', stripped)
        if first_match:
            group_name = f"Build progress [starting at {first_match.group(1)}/{first_match.group(2)}]"
        else:
            group_name = "Build progress"
        self.start_group(group_name)
        self.group_open = True

    def open_group_for_block(self, start_line: str):
        """Open a GitHub Actions log group for a block using its starting line.

        Precondition: no group is currently open (caller closed it if necessary).
        The group title is exactly the starting line (without the trailing newline).
        Callers should not print the starting line again inside the group to avoid duplication.
        """
        self.start_group(start_line.rstrip('\n'))
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
        """Process a single line of output via an explicit finite state machine, streaming output immediately.

        (Implementation detail) State machine overview:
        - States:
            - OUTSIDE: No open group and not collecting lines into a block.
            - GROUP_OPEN: A ::group:: for normal ✔ lines is open.
            - IN_WARNING: Collecting a warning block (⚠ line + following lines); a block ::group:: is open.
            - IN_ERROR: Collecting an error block (✖ line + following lines); a block ::group:: is open.
            - IN_INFO: Collecting an info block (ℹ line + following lines); a block ::group:: is open.

        - Events (one for each new output line)
            - NORMAL: Line starts with ✔
            - NEW_WARNING: Line starts with ⚠
            - NEW_ERROR: Line starts with ✖
            - NEW_INFO: Line starts with ℹ
            - OTHER: Any other line (including end-of-build summary lines)
            - EOF: End of build output

        - Transitions (current state + event → sequence; of; actions → next state)
            - OUTSIDE + NORMAL → open_group; print → GROUP_OPEN
            - OUTSIDE + NEW_* → start_block; print → IN_*
            - OUTSIDE + OTHER → print → OUTSIDE
            - GROUP_OPEN + NORMAL → print → GROUP_OPEN
            - GROUP_OPEN + NEW_*/OTHER → close_group; (open block group + start_block if NEW_*); print → IN_* or OUTSIDE
            - IN_* + NORMAL → flush_block (closes block group); open_group; print → GROUP_OPEN
            - IN_* + NEW_* → flush_block (closes previous block group); open block group + start_block; print → IN_*
            - IN_* + OTHER → if summary-line then flush_block else append_block; print → OUTSIDE or IN_*
            - * + EOF → flush_block; close_group
        """

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
                self.current_block = [line]
                self.open_group_for_block(line)
                self.state = self.State.IN_WARNING
            elif evt == self.Evt.NEW_ERROR:
                self.current_block = [line]
                self.open_group_for_block(line)
                self.state = self.State.IN_ERROR
            elif evt == self.Evt.NEW_INFO:
                self.current_block = [line]
                self.open_group_for_block(line)
                self.state = self.State.IN_INFO
            elif evt == self.Evt.OTHER:
                print(line, end='', flush=True)
            return

        if self.state == self.State.GROUP_OPEN:
            if evt == self.Evt.NORMAL:
                print(line, end='', flush=True)
            else:
                # Close group, then handle the event outside the group
                self.close_group_if_open()
                if evt == self.Evt.NEW_WARNING:
                    self.current_block = [line]
                    self.open_group_for_block(line)
                    self.state = self.State.IN_WARNING
                elif evt == self.Evt.NEW_ERROR:
                    self.current_block = [line]
                    self.open_group_for_block(line)
                    self.state = self.State.IN_ERROR
                elif evt == self.Evt.NEW_INFO:
                    self.current_block = [line]
                    self.open_group_for_block(line)
                    self.state = self.State.IN_INFO
                else:
                    print(line, end='', flush=True)
                    self.state = self.State.OUTSIDE
            return

        if self.state in (self.State.IN_WARNING, self.State.IN_ERROR, self.State.IN_INFO):
            if evt == self.Evt.NORMAL:
                self.flush_block()
                self.open_group_for_line(line)
                print(line, end='', flush=True)
                self.state = self.State.GROUP_OPEN
            elif evt == self.Evt.NEW_WARNING:
                self.flush_block()
                self.current_block = [line]
                self.open_group_for_block(line)
                self.state = self.State.IN_WARNING
            elif evt == self.Evt.NEW_ERROR:
                self.flush_block()
                self.current_block = [line]
                self.open_group_for_block(line)
                self.state = self.State.IN_ERROR
            elif evt == self.Evt.NEW_INFO:
                self.flush_block()
                self.current_block = [line]
                self.open_group_for_block(line)
                self.state = self.State.IN_INFO
            else:  # OTHER → continuation or summary
                if self.is_build_summary(line):
                    self.flush_block()
                    print(line, end='', flush=True)
                    self.state = self.State.OUTSIDE
                else:
                    self.current_block.append(line)
                    print(line, end='', flush=True)
            return

    def flush_block(self):
        """Record the current warning/error block for the summary."""
        if not self.current_block:
            return

        block_text = ''.join(self.current_block)
        file_info = self.extract_file_info(self.current_block[0])

        # Extract actual info/warning/error messages
        messages = []
        for line in self.current_block:
            low = line.lower()
            if 'warning:' in low or 'error:' in low or 'info:' in low or 'trace:' in low:
                messages.append(line.strip())

        block_data = {
            'file_info': file_info,
            'messages': messages,
            'full_output': block_text
        }

        if self.state == self.State.IN_WARNING:
            self.warnings.append(block_data)
        elif self.state == self.State.IN_ERROR:
            self.errors.append(block_data)
        elif self.state == self.State.IN_INFO:
            self.infos.append(block_data)

        # Close any open group for this block; lines were already streamed.
        self.close_group_if_open()
        # Do not print here; lines were already streamed as they arrived.
        self.current_block = []
        self.state = self.State.OUTSIDE

    def finalize(self):
        """Finalize processing"""
        self.flush_block()
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
    if len(sys.argv) < 3:
        print("Usage: lake-build-wrapper.py <output_file.json> <command> [args...]", file=sys.stderr)
        sys.exit(1)

    processor = BuildOutputProcessor()

    # Run the command and process output line by line
    process = subprocess.Popen(
        sys.argv[2:],
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

        # Write summary as JSON string
        summary = processor.get_summary()
        summary_file = sys.argv[1]
        with open(summary_file, 'w') as f:
            json.dump(summary, f)

        # Exit with the same code as the subprocess
        sys.exit(process.returncode)

    except KeyboardInterrupt:
        process.terminate()
        sys.exit(130)

if __name__ == "__main__":
    main()
