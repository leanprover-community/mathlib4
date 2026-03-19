#!/usr/bin/env python3
"""Shared configuration and helpers for set_option scripts."""

import re
import subprocess
from pathlib import Path

PROJECT_DIR = Path(__file__).resolve().parent.parent

DEFAULT_OPTIONS = [
    "backward.isDefEq.respectTransparency",
    "backward.whnf.reducibleClassField",
]


def set_option_line(option: str, value: str = "false") -> str:
    """Return the set_option line text for an option."""
    return f"set_option {option} {value} in\n"


def removable_pattern(option: str, value: str = "false") -> re.Pattern:
    """Match bare `set_option X <value> in` lines (no trailing comment)."""
    escaped = re.escape(option)
    escaped_val = re.escape(value)
    return re.compile(rf"^\s*set_option {escaped} {escaped_val} in\s*$")


def commented_pattern(option: str, value: str = "false") -> re.Pattern:
    """Match `set_option X <value> in -- ...` lines."""
    escaped = re.escape(option)
    escaped_val = re.escape(value)
    return re.compile(rf"^\s*set_option {escaped} {escaped_val} in\s+--")


def lakefile_pattern(option: str, value: str = "false") -> re.Pattern:
    """Match lakefile entries for an option."""
    escaped = re.escape(option)
    escaped_val = re.escape(value)
    return re.compile(
        rf"^\s*⟨`{escaped},\s*{escaped_val}⟩,?\s*\n",
        re.MULTILINE,
    )


PROGRESS_RE = re.compile(r"\[(\d+)/(\d+)\]")


def lake_build_with_progress(project_dir: Path) -> tuple[int, str]:
    """Run ``lake build`` with a progress display.

    Returns (returncode, captured_output).
    """
    proc = subprocess.Popen(
        ["lake", "build"],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        cwd=project_dir,
    )
    output_lines: list[str] = []
    for line in proc.stdout:
        output_lines.append(line)
        m = PROGRESS_RE.search(line)
        if m:
            print(f"\r  [{m.group(1)}/{m.group(2)}]", end="", flush=True)
    proc.wait()
    print()  # newline after progress
    return proc.returncode, "".join(output_lines)
