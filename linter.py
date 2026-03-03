#!/usr/bin/env python3
"""
Automatically fix mathlib definitions by adding @[implicit_reducible] annotations.

This script:
1. Runs `lake build`
2. Parses error output for definitions missing @[implicit_reducible]
3. Finds the 'def' keyword at or after the reported line
4. Adds the annotation before that 'def' line
5. Stops after one iteration for review
"""

import re
import subprocess
import sys
from pathlib import Path
from typing import List, Tuple


class MathLibFixer:
    def __init__(self, mathlib_root: Path):
        self.mathlib_root = mathlib_root
        self.error_pattern = re.compile(
            r"error: (.+?):(\d+):\d+: definition `([^`]+)` returns a class but is not marked @\[reducible\] or @\[implicit_reducible\]\."
        )
        self.iteration = 0
        self.total_fixes = 0

    def run_build(self) -> str:
        """Run `lake build` and return the output."""
        print("\n" + "=" * 80)
        print(f"Iteration {self.iteration + 1}: Running `lake build`...")
        print("=" * 80)

        try:
            result = subprocess.run(
                ["lake", "build"],
                cwd=self.mathlib_root,
                capture_output=True,
                text=True,
                timeout=600  # 10 minute timeout
            )
            # Combine stdout and stderr since lake outputs to both
            output = result.stdout + result.stderr
            return output
        except subprocess.TimeoutExpired:
            print("ERROR: Build timed out after 10 minutes")
            sys.exit(1)
        except FileNotFoundError:
            print("ERROR: `lake` command not found. Is Lake installed and in PATH?")
            sys.exit(1)

    def _try_relative_path(self, file_path: Path) -> Path:
        """Try to return a relative path, or the absolute path if that fails."""
        try:
            return file_path.relative_to(self.mathlib_root)
        except ValueError:
            return file_path

    def parse_errors(self, output: str) -> List[Tuple[Path, int, str]]:
        """Parse build output and extract (file_path, line_number, definition_name) tuples for errors."""
        errors = []
        for match in self.error_pattern.finditer(output):
            file_path_str = match.group(1)
            line_number = int(match.group(2))
            definition_name = match.group(3)

            # Convert to absolute path if necessary
            file_path = Path(file_path_str)
            if not file_path.is_absolute():
                file_path = self.mathlib_root / file_path

            errors.append((file_path, line_number, definition_name))
            rel_path = self._try_relative_path(file_path)
            print(f"  Found error: {rel_path}:{line_number}")

        # Sort by file path, then by line number in DESCENDING order
        # This ensures that when we insert annotations, we process from bottom to top
        # within each file, so line number shifts don't affect subsequent insertions
        errors.sort(key=lambda x: (x[0], -x[1]))

        return errors

    def _add_to_attribute_block(self, attr_line: str) -> str:
        """
        Add implicit_reducible to an existing attribute block.
        Special case: if to_additive is present, add it as to_additive (attr := implicit_reducible)
        """
        attr_stripped = attr_line.lstrip()
        indent = len(attr_line) - len(attr_stripped)
        indent_str = ' ' * indent

        # Check if to_additive is in the attribute block
        if 'to_additive' in attr_stripped:
            # Find the position of 'to_additive'
            to_additive_pos = attr_stripped.find('to_additive')
            before_to_additive = attr_stripped[:to_additive_pos]
            after_to_additive = attr_stripped[to_additive_pos + len('to_additive'):]

            # Check if to_additive already has parentheses
            if after_to_additive.lstrip().startswith('('):
                # to_additive (something) - we need to add attr := implicit_reducible inside
                # Find the closing parenthesis
                open_paren = after_to_additive.find('(')
                close_paren = after_to_additive.find(')')
                if close_paren != -1:
                    inside_parens = after_to_additive[open_paren + 1:close_paren]
                    rest = after_to_additive[close_paren:]
                    new_attr_line = f"{indent_str}{before_to_additive}to_additive ({inside_parens}, attr := implicit_reducible){rest}"
                    return new_attr_line
            else:
                # to_additive without parentheses or with space - add as to_additive (attr := implicit_reducible)
                # Find what comes after to_additive
                rest = after_to_additive
                new_attr_line = f"{indent_str}{before_to_additive}to_additive (attr := implicit_reducible){rest}"
                return new_attr_line

        # No to_additive, just add implicit_reducible at the start
        return f"{indent_str}@[implicit_reducible, {attr_stripped[2:]}"

    def add_annotation(self, file_path: Path, line_number: int, definition_name: str) -> bool:
        """
        Add @[implicit_reducible] annotation before the first 'def', 'noncomputable def',
        'protected def', or 'protected noncomputable def' line at or after the reported line.

        Handles three cases:
        1. If the def line has @[...] attributes, add implicit_reducible to that block
        2. If the line before def has @[...], add implicit_reducible to that block
        3. Otherwise, insert a new line with @[implicit_reducible] before the def

        Returns True if successful, False otherwise.
        """
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()

            # Convert to 0-indexed
            start_index = line_number - 1

            if start_index < 0 or start_index >= len(lines):
                print(f"    ERROR: Line {line_number} out of range in {file_path}")
                return False

            # Search forward from the error line to find the first line starting with 'def', 'noncomputable def', 'protected def', or 'protected noncomputable def'
            def_index = None
            for i in range(start_index, len(lines)):
                stripped = lines[i].lstrip()
                if (stripped.startswith('def ') or
                    stripped.startswith('noncomputable def ') or
                    stripped.startswith('protected def ') or
                    stripped.startswith('protected noncomputable def ')):
                    def_index = i
                    break

            if def_index is None:
                print(f"    ERROR: Could not find 'def' keyword at or after line {line_number} in {file_path}")
                return False

            def_line = lines[def_index]
            def_stripped = def_line.lstrip()

            # Check if the def line itself starts with @[...] attributes
            if def_stripped.startswith('@['):
                # Find the closing bracket of the attribute block
                closing_bracket_idx = def_stripped.find(']')
                if closing_bracket_idx != -1:
                    # Insert implicit_reducible using the helper method
                    new_def_line = self._add_to_attribute_block(def_line)
                    lines[def_index] = new_def_line

                    with open(file_path, 'w', encoding='utf-8', newline='') as f:
                        f.writelines(lines)

                    file_rel = self._try_relative_path(file_path)
                    print(f"    ✓ Fixed Definition {definition_name} at Line {def_index + 1} of File {file_rel}")
                    return True

            # Check if the line before the def has @[...] attributes
            if def_index > 0:
                prev_line = lines[def_index - 1]
                prev_stripped = prev_line.lstrip()

                if prev_stripped.startswith('@['):
                    # Find the closing bracket of the attribute block
                    closing_bracket_idx = prev_stripped.find(']')
                    if closing_bracket_idx != -1:
                        # Insert implicit_reducible using the helper method
                        new_prev_line = self._add_to_attribute_block(prev_line)
                        lines[def_index - 1] = new_prev_line

                        with open(file_path, 'w', encoding='utf-8', newline='') as f:
                            f.writelines(lines)

                        file_rel = self._try_relative_path(file_path)
                        print(f"    ✓ Fixed Definition {definition_name} at Line {def_index + 1} of File {file_rel}")
                        return True

            # No existing attributes found, add a new line with @[implicit_reducible]
            indent = len(def_line) - len(def_stripped)
            indent_str = ' ' * indent
            annotation_line = f"{indent_str}@[implicit_reducible]\n"

            # Check if annotation already exists (safety check)
            if def_index > 0 and "@[implicit_reducible]" in lines[def_index - 1]:
                print(f"    WARNING: @[implicit_reducible] already present before line {def_index + 1} in {file_path}")
                return False

            # Insert the annotation
            lines.insert(def_index, annotation_line)

            with open(file_path, 'w', encoding='utf-8', newline='') as f:
                f.writelines(lines)

            file_rel = self._try_relative_path(file_path)
            actual_def_line = def_index + 1  # +1 to convert to 1-indexed
            print(f"    ✓ Fixed Definition {definition_name} at Line {actual_def_line} of File {file_rel}")
            return True

        except Exception as e:
            print(f"    ERROR: Failed to fix {file_path}:{line_number} - {e}")
            return False

    def run(self) -> None:
        """Main loop: build, parse errors, fix files, and stop for review."""
        self.iteration += 1

        # Run build
        output = self.run_build()

        # Parse errors
        errors = self.parse_errors(output)

        if not errors:
            print("\n" + "=" * 80)
            print("✓ SUCCESS: No @[implicit_reducible] errors found!")
            print(f"  Total fixes applied: {self.total_fixes}")
            print("=" * 80)
            return

        print(f"\nFound {len(errors)} error(s) to fix in this iteration")

        # Fix files
        fixed_count = 0
        for file_path, line_number, definition_name in errors:
            if self.add_annotation(file_path, line_number, definition_name):
                fixed_count += 1
                self.total_fixes += 1

        if fixed_count == 0:
            print("\nERROR: Found errors but failed to fix any of them.")
            return

        print(f"\nFixed {fixed_count} error(s). Stopping for review.")
        print("Run the script again after reviewing the changes.")


def main():
    if len(sys.argv) < 2:
        # Try to detect mathlib root (current directory or parent)
        mathlib_root = Path.cwd()
        if not (mathlib_root / "lakefile.lean").exists():
            print("Usage: python fix_mathlib.py <path_to_mathlib>")
            print("\nOr run from the mathlib root directory (containing lakefile.lean)")
            sys.exit(1)
    else:
        mathlib_root = Path(sys.argv[1]).resolve()
        if not mathlib_root.exists():
            print(f"ERROR: Path does not exist: {mathlib_root}")
            sys.exit(1)

    # Verify this looks like a mathlib repository
    if not (mathlib_root / "lakefile.lean").exists():
        print(f"ERROR: {mathlib_root} doesn't appear to be a mathlib root (no lakefile.lean found)")
        sys.exit(1)

    print(f"Starting mathlib fixer for: {mathlib_root}")
    print(f"This will run `lake build` once and fix errors.\n")

    fixer = MathLibFixer(mathlib_root)
    fixer.run()


if __name__ == "__main__":
    main()
