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
            GROUP_OPEN = auto()  # progress (✔) group is open
            IN_BLOCK = auto()    # inside an ℹ/⚠/✖ block group
        self.State = _State
        self.state = self.State.OUTSIDE

        class _BlockKind(Enum):
            INFO = auto()
            WARNING = auto()
            ERROR = auto()
        self.BlockKind = _BlockKind
        self.current_kind = None  # type: _BlockKind | None
        self.block_lists = {
            self.BlockKind.INFO: self.infos,
            self.BlockKind.WARNING: self.warnings,
            self.BlockKind.ERROR: self.errors,
        }

    def start_group(self, name: str):
        """Start a GitHub Actions log group"""
        print(f"::group::{name}", flush=True)

    def close_group(self):
        """Close the current log group.

        Precondition: a group is currently open.
        """
        print("::endgroup::", flush=True)
        self.group_open = False

    def open_group_for_normal_line(self, line: str):
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
        The group title is the starting line (without the trailing newline),
        colorized by kind: info=light blue, warning=yellow, error=red.
        Callers should not print the starting line again inside the group to avoid duplication.
        """
        title = start_line.rstrip('\n')
        # Colorize the title based on the current block kind.
        # INFO → light blue (94), WARNING → yellow (33), ERROR → red (31)
        color_code = None
        if self.current_kind == self.BlockKind.INFO:
            color_code = '94'
        elif self.current_kind == self.BlockKind.WARNING:
            color_code = '33'
        elif self.current_kind == self.BlockKind.ERROR:
            color_code = '31'
        if color_code is not None:
            title = f"\x1b[{color_code}m{title}\x1b[0m"
        self.start_group(title)
        self.group_open = True

    def is_normal_line(self, line: str) -> bool:
        """Check if line is normal build output (checkmark)."""
        return line.strip().startswith('✔')

    def detect_block_kind(self, line: str):
        """Return the BlockKind if the line starts a block; otherwise None."""
        stripped = line.strip()
        if stripped.startswith('⚠'):
            return self.BlockKind.WARNING
        if stripped.startswith('✖'):
            return self.BlockKind.ERROR
        if stripped.startswith('ℹ'):
            return self.BlockKind.INFO
        return None

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
        """Process one output line with a simple state machine and stream output.

        States
        - OUTSIDE: No group open, not collecting a block.
        - GROUP_OPEN: A progress (✔) ::group:: is open.
        - IN_BLOCK: Inside an ℹ/⚠/✖ block ::group::; `current_kind` is set.

        Classification
        - `is_normal_line(line)` detects ✔ lines.
        - `detect_block_kind(line)` detects ℹ/⚠/✖ starts (returns None otherwise).

        Transitions (current state → next)
        - OUTSIDE
          - normal → open progress group; print → GROUP_OPEN
          - block start → open block group (title is starting line); do not echo start line → IN_BLOCK
          - other → print → OUTSIDE
        - GROUP_OPEN
          - normal → print → GROUP_OPEN
          - block start → close progress group; open block group → IN_BLOCK
          - other → close progress group; print → OUTSIDE
        - IN_BLOCK
          - normal → flush block (records JSON, closes block group); open progress group; print → GROUP_OPEN
          - block start → flush block; open new block group → IN_BLOCK
          - other → if build summary then flush block and print (→ OUTSIDE) else append to block and print (→ IN_BLOCK)

        EOF is handled by `finalize()`: flush any open block and close any open group.
        """

        block_kind = self.detect_block_kind(line)
        is_normal = self.is_normal_line(line)

        if self.state == self.State.OUTSIDE:
            if is_normal:
                self.open_group_for_normal_line(line)
                print(line, end='', flush=True)
                self.state = self.State.GROUP_OPEN
            elif block_kind is not None:
                self.current_kind = block_kind
                self.current_block = [line]
                self.open_group_for_block(line)
                self.state = self.State.IN_BLOCK
            else:
                print(line, end='', flush=True)
            return

        if self.state == self.State.GROUP_OPEN:
            if is_normal:
                print(line, end='', flush=True)
            else:
                self.close_group()
                if block_kind is not None:
                    self.current_kind = block_kind
                    self.current_block = [line]
                    self.open_group_for_block(line)
                    self.state = self.State.IN_BLOCK
                else:
                    print(line, end='', flush=True)
                    self.state = self.State.OUTSIDE
            return

        if self.state == self.State.IN_BLOCK:
            if is_normal:
                self.flush_block()
                self.open_group_for_normal_line(line)
                print(line, end='', flush=True)
                self.state = self.State.GROUP_OPEN
            elif block_kind is not None:
                self.flush_block()
                self.current_kind = block_kind
                self.current_block = [line]
                self.open_group_for_block(line)
                self.state = self.State.IN_BLOCK
            else:
                if self.is_build_summary(line):
                    self.flush_block()
                    print(line, end='', flush=True)
                    self.state = self.State.OUTSIDE
                else:
                    self.current_block.append(line)
                    print(line, end='', flush=True)
            return

    def flush_block(self):
        """Record the current ℹ/⚠/✖ block for the summary and close its group."""
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

        if self.current_kind is not None:
            self.block_lists[self.current_kind].append(block_data)

        # Close the group for this block; lines were already streamed.
        self.close_group()
        # Do not print here; lines were already streamed as they arrived.
        self.current_block = []
        self.current_kind = None
        self.state = self.State.OUTSIDE

    def finalize(self):
        """Finalize processing"""
        self.flush_block()
        if self.group_open:
            self.close_group()

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
