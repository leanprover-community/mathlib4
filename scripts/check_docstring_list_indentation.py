#!/usr/bin/env python3
"""
Detect suspicious indentation in Markdown list items inside Lean docstrings.

The checker looks for ordered and unordered list items whose continuation lines
appear to be wrapped text but are not indented enough to remain in the same
Markdown list item.

Typical usage:

    python3 scripts/check_docstring_list_indentation.py
    python3 scripts/check_docstring_list_indentation.py Mathlib Archive
    python3 scripts/check_docstring_list_indentation.py Mathlib --fix --confidence high
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path


UNORDERED_ITEM_RE = re.compile(r"^(?P<indent>[ ]{0,3})(?P<marker>[-+*])(?P<pad>[ ]+)(?P<text>.*)$")
ORDERED_ITEM_RE = re.compile(r"^(?P<indent>[ ]{0,3})(?P<marker>\d+[.)])(?P<pad>[ ]+)(?P<text>.*)$")
BLOCKQUOTE_RE = re.compile(r"^[ ]{0,3}>")
HEADING_RE = re.compile(r"^[ ]{0,3}#{1,6}(?:\s|$)")
FENCE_RE = re.compile(r"^(?P<indent>[ ]{0,3})(?P<fence>`{3,}|~{3,})")
ITEM_FENCE_RE = re.compile(r"^(?P<fence>`{3,}|~{3,})")
THEMATIC_BREAK_RE = re.compile(r"^[ ]{0,3}(?:(?:\*\s*){3,}|(?:-\s*){3,}|(?:_\s*){3,})$")


@dataclass(frozen=True)
class Docstring:
    path: Path
    start_line: int
    lines: list[str]


@dataclass(frozen=True)
class Finding:
    path: Path
    line: int
    required_indent: int
    actual_indent: int
    item_line: int
    item_marker: str
    item_text: str
    continuation: str
    confidence: str


def iter_lean_files(paths: list[Path]) -> list[Path]:
    out: list[Path] = []
    for path in paths:
        if path.is_file() and path.suffix == ".lean":
            out.append(path)
            continue
        if path.is_dir():
            out.extend(sorted(path.rglob("*.lean")))
    return out


def extract_docstrings(text: str, path: Path) -> list[Docstring]:
    """
    Extract `/-! ... -/` and `/-- ... -/` comments, keeping starting line numbers.

    We only need a lightweight parser: nested comments are handled by tracking depth.
    """
    docstrings: list[Docstring] = []
    i = 0
    line = 1
    n = len(text)

    while i < n:
        if text.startswith("/--", i) or text.startswith("/-!", i):
            i += 3
            content_start_line = line
            content_start_index = i
            depth = 1
            while i < n and depth > 0:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                    continue
                if text.startswith("-/", i):
                    depth -= 1
                    i += 2
                    continue
                if text[i] == "\n":
                    line += 1
                i += 1
            if depth != 0:
                break
            content_end_index = i - 2
            content = text[content_start_index:content_end_index]
            docstrings.append(
                Docstring(path=path, start_line=content_start_line, lines=content.splitlines())
            )
            continue

        if text[i] == "\n":
            line += 1
        i += 1

    return docstrings


def leading_spaces(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def list_item_match(line: str) -> re.Match[str] | None:
    return UNORDERED_ITEM_RE.match(line) or ORDERED_ITEM_RE.match(line)


def is_block_start(line: str, *, include_fences: bool) -> bool:
    stripped = line.strip()
    if stripped == "":
        return False
    if include_fences:
        return bool(
            list_item_match(line)
            or BLOCKQUOTE_RE.match(line)
            or HEADING_RE.match(line)
            or THEMATIC_BREAK_RE.match(line)
        )
    return bool(
        list_item_match(line)
        or BLOCKQUOTE_RE.match(line)
        or HEADING_RE.match(line)
        or THEMATIC_BREAK_RE.match(line)
        or FENCE_RE.match(line)
    )


def looks_like_continuation(line: str) -> bool:
    return line.lstrip() != ""


def classify_confidence(item_line: str, continuation_line: str) -> str:
    """
    Heuristic confidence:
    - high: likely wrapped continuation within the same list item
    - ambiguous: could be stylistic paragraphing after a list item
    """
    stripped = continuation_line.lstrip()
    if stripped == "":
        return "ambiguous"
    first = stripped[0]
    starts_mid_sentence = first.islower() or first.isdigit() or stripped.startswith(("`", "("))
    item_ends_sentence = item_line.rstrip().endswith((".", "!", "?"))
    if starts_mid_sentence and not item_ends_sentence:
        return "high"
    return "ambiguous"


def find_bad_list_indentation(docstring: Docstring, *, include_fences: bool) -> list[Finding]:
    findings: list[Finding] = []
    lines = docstring.lines
    in_fence = False
    fence_char = ""

    for idx, line in enumerate(lines):
        fence_match = FENCE_RE.match(line)
        if fence_match:
            fence = fence_match.group("fence")
            if not in_fence:
                in_fence = True
                fence_char = fence[0]
            elif fence_char == fence[0]:
                in_fence = False
                fence_char = ""
            continue
        if in_fence:
            continue

        item_match = list_item_match(line)
        if item_match is None:
            continue

        item_indent = len(item_match.group("indent"))
        item_marker = item_match.group("marker")
        required_indent = item_indent + len(item_marker) + len(item_match.group("pad"))
        item_text = item_match.group("text")
        item_line = docstring.start_line + idx

        j = idx + 1
        in_cont_fence = False
        cont_fence_char = ""
        if include_fences:
            item_fence_match = ITEM_FENCE_RE.match(item_text.lstrip())
            if item_fence_match:
                in_cont_fence = True
                cont_fence_char = item_fence_match.group("fence")[0]
        while j < len(lines):
            next_line = lines[j]
            fence_match_next = FENCE_RE.match(next_line)
            if next_line.strip() == "" and not (include_fences and in_cont_fence):
                break
            if not in_cont_fence and is_block_start(next_line, include_fences=include_fences):
                break

            actual_indent = leading_spaces(next_line)
            if actual_indent < required_indent and looks_like_continuation(next_line):
                confidence = classify_confidence(line, next_line)
                findings.append(
                    Finding(
                        path=docstring.path,
                        line=docstring.start_line + j,
                        required_indent=required_indent,
                        actual_indent=actual_indent,
                        item_line=item_line,
                        item_marker=item_marker,
                        item_text=item_text.strip(),
                        continuation=next_line.strip(),
                        confidence=confidence,
                    )
                )
            if include_fences and fence_match_next:
                fence = fence_match_next.group("fence")
                if not in_cont_fence:
                    in_cont_fence = True
                    cont_fence_char = fence[0]
                elif cont_fence_char == fence[0]:
                    in_cont_fence = False
                    cont_fence_char = ""
            j += 1

    return findings


def run(paths: list[Path], *, include_fences: bool) -> list[Finding]:
    findings: list[Finding] = []
    for path in iter_lean_files(paths):
        text = path.read_text(encoding="utf-8")
        docstrings = extract_docstrings(text, path)
        for docstring in docstrings:
            findings.extend(find_bad_list_indentation(docstring, include_fences=include_fences))
    return findings


def filter_findings(findings: list[Finding], confidence: str) -> list[Finding]:
    if confidence == "all":
        return findings
    return [f for f in findings if f.confidence == confidence]


def apply_fixes(findings: list[Finding]) -> tuple[int, int]:
    by_path: dict[Path, list[Finding]] = {}
    for finding in findings:
        by_path.setdefault(finding.path, []).append(finding)

    fixed_lines = 0
    fixed_files = 0
    for path, path_findings in by_path.items():
        lines = path.read_text(encoding="utf-8").splitlines(keepends=True)
        changed = False
        touched: set[int] = set()
        by_item: dict[tuple[int, int], list[Finding]] = {}
        for finding in path_findings:
            by_item.setdefault((finding.item_line, finding.required_indent), []).append(finding)

        for _, item_findings in sorted(by_item.items(), key=lambda kv: kv[0]):
            unique_indices = sorted({f.line - 1 for f in item_findings})
            deficits: list[int] = []
            for line_idx in unique_indices:
                if line_idx < 0 or line_idx >= len(lines) or line_idx in touched:
                    continue
                raw_line = lines[line_idx]
                if raw_line.strip() == "":
                    continue
                required_indent = item_findings[0].required_indent
                deficits.append(required_indent - leading_spaces(raw_line))
            if not deficits:
                continue
            shift = max(deficits)
            if shift <= 0:
                continue

            for line_idx in unique_indices:
                if line_idx < 0 or line_idx >= len(lines) or line_idx in touched:
                    continue
                raw_line = lines[line_idx]
                if raw_line.strip() == "":
                    continue
                new_line = " " * shift + raw_line
                if new_line != raw_line:
                    lines[line_idx] = new_line
                    fixed_lines += 1
                    changed = True
                    touched.add(line_idx)
        if changed:
            path.write_text("".join(lines), encoding="utf-8")
            fixed_files += 1
    return fixed_files, fixed_lines


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Detect likely bad indentation in Markdown list continuations "
            "inside Lean docstrings."
        )
    )
    parser.add_argument(
        "paths",
        nargs="*",
        default=["Mathlib"],
        help="Lean files or directories to scan (default: Mathlib).",
    )
    parser.add_argument(
        "--max",
        type=int,
        default=200,
        help="Maximum number of findings to print (default: 200).",
    )
    parser.add_argument(
        "--confidence",
        choices=["all", "high", "ambiguous"],
        default="all",
        help="Filter findings by confidence (default: all).",
    )
    parser.add_argument(
        "--fix",
        action="store_true",
        help="Apply indentation fixes in place for matching findings.",
    )
    parser.add_argument(
        "--include-fences",
        action="store_true",
        help=(
            "Also treat fenced code blocks as list continuations. "
            "This can report and fix indentation inside fenced blocks nested under list items."
        ),
    )
    args = parser.parse_args()

    findings = run([Path(p) for p in args.paths], include_fences=args.include_fences)
    selected = filter_findings(findings, args.confidence)
    if args.fix:
        fixed_files, fixed_lines = apply_fixes(selected)
        print(
            f"Applied {fixed_lines} fix(es) in {fixed_files} file(s) "
            f"(confidence filter: {args.confidence})."
        )
        # Recompute findings after in-place edits so output reflects current state.
        findings = run([Path(p) for p in args.paths], include_fences=args.include_fences)
        selected = filter_findings(findings, args.confidence)
    for finding in selected[: args.max]:
        print(
            f"{finding.path}:{finding.line}: "
            f"list continuation likely under-indented "
            f"(expected >= {finding.required_indent} spaces, found {finding.actual_indent}; "
            f"confidence: {finding.confidence})"
        )
        print(f"  item: {finding.item_line}: {finding.item_marker} {finding.item_text}")
        print(f"  line: {finding.line}: {finding.continuation}")

    if len(selected) > args.max:
        print(
            f"... and {len(selected) - args.max} more finding(s). "
            "Increase --max to see all."
        )
    return 1 if selected else 0


if __name__ == "__main__":
    sys.exit(main())
