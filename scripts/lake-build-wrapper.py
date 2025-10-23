#!/usr/bin/env python3
"""
Wrapper script for build output that:
1. Groups normal build output into collapsible log groups
2. Highlights warnings and errors
3. Extracts warnings/errors to JSON for step outputs
"""

import sys
import subprocess
import re
import json
from typing import Dict, Any

class BuildOutputProcessor:
    def __init__(self, group_size=1):
        self.warnings = []
        self.errors = []
        self.current_group_lines = []
        self.in_warning = False
        self.in_error = False
        self.current_issue = []
        self.group_size = group_size  # Flush groups after this many lines
        self.in_group = False

    def start_group(self, name: str):
        """Start a GitHub Actions log group"""
        print(f"::group::{name}", flush=True)

    def end_group(self):
        """End a GitHub Actions log group"""
        print("::endgroup::", flush=True)

    def flush_normal_group(self, force=False):
        """Flush accumulated normal output as a collapsed group"""
        if not self.current_group_lines:
            return

        # Only flush if we have enough lines or forced
        if not force and len(self.current_group_lines) < self.group_size:
            return

        # If not already in a group, start one
        if not self.in_group:
            first_line = self.current_group_lines[0].strip()
            first_match = re.search(r'\[(\d+)/(\d+)\]', first_line)

            if first_match:
                group_name = f"Build progress [starting at {first_match.group(1)}/{first_match.group(2)}]"
            else:
                group_name = "Build progress"

            self.start_group(group_name)
            self.in_group = True

        # Print accumulated lines
        for line in self.current_group_lines:
            print(line, end='', flush=True)
        self.current_group_lines = []

        # If forced (end of group), close the group
        if force and self.in_group:
            self.end_group()
            self.in_group = False

    def is_normal_line(self, line: str) -> bool:
        """Check if line is normal build output (checkmark)"""
        return line.strip().startswith('✔')

    def is_warning_start(self, line: str) -> bool:
        """Check if line starts a warning"""
        return line.strip().startswith('⚠')

    def is_error_start(self, line: str) -> bool:
        """Check if line starts an error"""
        return line.strip().startswith('✖')

    def is_build_summary(self, line: str) -> bool:
        """Check if line is a build summary (end of build output)"""
        stripped = line.strip()
        return (stripped.startswith('error: build failed') or
                stripped.startswith('Build completed successfully') or
                stripped.startswith('Some required targets logged failures:') or
                stripped.startswith('Error: Process completed with exit code'))

    def extract_file_info(self, line: str) -> Dict[str, Any]:
        """Extract file information from build line"""
        match = re.search(r'\[(\d+)/(\d+)\]\s+(?:Built|Building)\s+([\w.]+)', line)
        if match:
            return {
                'current': int(match.group(1)),
                'total': int(match.group(2)),
                'file': match.group(3)
            }
        return {}

    def process_line(self, line: str):
        """Process a single line of output"""
        # Check for build summary lines - these end any current issue and print directly
        if self.is_build_summary(line):
            self.flush_issue()
            self.flush_normal_group(force=True)
            print(line, end='', flush=True)
            return

        # Check if we're starting a warning or error
        if self.is_warning_start(line):
            self.flush_issue()  # Flush any previous issue first
            self.flush_normal_group(force=True)
            self.in_warning = True
            self.current_issue = [line]
            return

        if self.is_error_start(line):
            self.flush_issue()  # Flush any previous issue first
            self.flush_normal_group(force=True)
            self.in_error = True
            self.current_issue = [line]
            return

        # If we're in a warning or error, accumulate lines
        if self.in_warning or self.in_error:
            # Check if we've reached the end (next normal/warning/error line)
            if self.is_normal_line(line) or self.is_warning_start(line) or self.is_error_start(line):
                self.flush_issue()
                # Process this line as a new item
                if self.is_warning_start(line):
                    self.in_warning = True
                    self.current_issue = [line]
                elif self.is_error_start(line):
                    self.in_error = True
                    self.current_issue = [line]
                else:
                    self.current_group_lines.append(line)
                    self.flush_normal_group()  # Try to flush (will only flush if enough lines)
            else:
                self.current_issue.append(line)
            return

        # Normal output
        if self.is_normal_line(line):
            self.current_group_lines.append(line)
            self.flush_normal_group()  # Try to flush (will only flush if enough lines)
        else:
            # Non-build line (could be part of ongoing issue or standalone)
            if self.current_group_lines or self.in_group:
                self.current_group_lines.append(line)
                self.flush_normal_group()  # Try to flush
            else:
                print(line, end='', flush=True)

    def flush_issue(self):
        """Flush accumulated warning or error"""
        if not self.current_issue:
            return

        issue_text = ''.join(self.current_issue)
        file_info = self.extract_file_info(self.current_issue[0])

        # Extract actual warning/error messages
        messages = []
        for line in self.current_issue:
            if 'warning:' in line.lower() or 'error:' in line.lower():
                messages.append(line.strip())

        issue_data = {
            'file_info': file_info,
            'messages': messages,
            'full_output': issue_text
        }

        if self.in_warning:
            self.warnings.append(issue_data)
            self.in_warning = False
        elif self.in_error:
            self.errors.append(issue_data)
            self.in_error = False

        # Print the issue outside of any group
        print(issue_text, end='', flush=True)
        self.current_issue = []

    def finalize(self):
        """Finalize processing"""
        self.flush_issue()
        self.flush_normal_group(force=True)

    def get_summary(self) -> Dict[str, Any]:
        """Get summary of warnings and errors"""
        return {
            'warnings': self.warnings,
            'errors': self.errors,
            'warning_count': len(self.warnings),
            'error_count': len(self.errors)
        }

def main():
    if len(sys.argv) < 2:
        print("Usage: wrapper.py <command> [args...]", file=sys.stderr)
        print("Options: Set GROUP_SIZE env var to control grouping (default: 1)", file=sys.stderr)
        sys.exit(1)

    # Allow customizing group size via environment variable
    import os
    group_size = int(os.environ.get('GROUP_SIZE', '1'))
    processor = BuildOutputProcessor(group_size=group_size)

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
                # For multiline output, use delimiter syntax
                f.write(f"summary<<EOF\n{summary_json}\nEOF\n")
        else:
            print("Warning: GITHUB_OUTPUT environment variable not set", file=sys.stderr)
            print(f"warning_count={summary['warning_count']}", file=sys.stderr)
            print(f"error_count={summary['error_count']}", file=sys.stderr)
            print(f"summary={summary_json}", file=sys.stderr)

        # Exit with the same code as the subprocess
        sys.exit(process.returncode)

    except KeyboardInterrupt:
        process.terminate()
        sys.exit(130)

if __name__ == "__main__":
    main()
