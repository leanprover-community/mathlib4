#!/usr/bin/env python3
"""
Format Lean doc comments (`/-- ... -/` and `/-! ... -/`) with mdformat.

Run with:
    uv run --with mdformat python scripts/mdformat_docstrings.py --write Mathlib
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import sys
from typing import Iterable

import mdformat
from markdown_it import MarkdownIt


@dataclass(frozen=True)
class DocComment:
    start: int
    end: int
    opener: str


LIST_ITEM_MARKER_RE = re.compile(r"^([ \t]*(?:>[ \t]*)*)([ \t]*)([-*+])([ \t]+)(.*)$")
MASK_TOKEN_PREFIX = "MDMASKTOKEN"


def iter_lean_files(paths: Iterable[Path]) -> list[Path]:
    files: list[Path] = []
    for path in paths:
        if path.is_file() and path.suffix == ".lean":
            files.append(path)
            continue
        if path.is_dir():
            files.extend(sorted(path.rglob("*.lean")))
    return sorted(files)


def _skip_string(src: str, i: int) -> int:
    # `i` points at the opening `"` and we return the first char after the string literal.
    assert src[i] == '"'
    i += 1
    n = len(src)
    while i < n:
        ch = src[i]
        if ch == "\\":
            i += 2
            continue
        if ch == '"':
            return i + 1
        i += 1
    return n


def _skip_line_comment(src: str, i: int) -> int:
    # `i` points at `--`.
    n = len(src)
    j = src.find("\n", i + 2)
    return n if j == -1 else j + 1


def find_doc_comments(src: str) -> list[DocComment]:
    comments: list[DocComment] = []
    i = 0
    n = len(src)
    while i < n:
        if src[i] == '"':
            i = _skip_string(src, i)
            continue
        if src.startswith("--", i):
            i = _skip_line_comment(src, i)
            continue
        if src.startswith("/-", i):
            opener = src[i : i + 3]
            is_doc = opener in {"/--", "/-!"}
            start = i
            i += 2
            depth = 1
            while i < n and depth > 0:
                if src.startswith("/-", i):
                    depth += 1
                    i += 2
                elif src.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth == 0 and is_doc:
                comments.append(DocComment(start=start, end=i, opener=opener))
            continue
        i += 1
    return comments


def line_indent_before(src: str, pos: int) -> str:
    line_start = src.rfind("\n", 0, pos) + 1
    prefix = src[line_start:pos]
    return re.match(r"[ \t]*", prefix).group(0)  # type: ignore[union-attr]


def strip_prefix_once(s: str, prefix: str) -> str:
    if prefix and s.startswith(prefix):
        return s[len(prefix) :]
    return s


def split_outer_whitespace(inner: str) -> tuple[str, str, str]:
    start = 0
    while start < len(inner) and inner[start] in {" ", "\n", "\t"}:
        start += 1
    end = len(inner)
    while end > start and inner[end - 1] in {" ", "\n", "\t"}:
        end -= 1
    return inner[:start], inner[start:end], inner[end:]


def mask_risky_fragments(md: str) -> tuple[str, dict[str, str]]:
    token_map: dict[str, str] = {}
    token_counter = 0

    def make_token() -> str:
        nonlocal token_counter
        token = f"{MASK_TOKEN_PREFIX}{token_counter:06d}"
        token_counter += 1
        return token

    def mask_with_pattern(text: str, pattern: str, *, flags: int = 0) -> str:
        def repl(match: re.Match[str]) -> str:
            token = make_token()
            token_map[token] = match.group(0)
            return token

        return re.sub(pattern, repl, text, flags=flags)

    masked = md
    # Mask display math first, then inline math.
    masked = mask_with_pattern(masked, r"\$\$(?:.|\n)*?\$\$", flags=re.DOTALL)
    masked = mask_with_pattern(masked, r"(?<!\$)\$(?!\$)(?:\\.|[^$\n\\])*(?<!\\)\$(?!\$)")
    # Reference-link definitions and uses.
    masked = mask_with_pattern(masked, r"(?m)^\[[^\]\n]+\]:[^\n]*$")
    masked = mask_with_pattern(masked, r"\[[^\]\n]+\]\[[^\]\n]*\]")
    # Backslash-heavy TeX fragments outside explicit math/reference-link forms.
    masked = mask_with_pattern(masked, r"\\[A-Za-z]+")
    masked = mask_with_pattern(masked, r"\\[\[\]\(\){}_^]")
    return masked, token_map


def unmask_fragments(md: str, token_map: dict[str, str]) -> str:
    if not token_map:
        return md
    out = md
    for token, original in token_map.items():
        out = out.replace(token, original)
    return out


def drop_new_escaped_brackets(original: str, formatted: str) -> str:
    def drop_extra(text: str, esc: str, plain: str, keep_count: int) -> str:
        i = 0
        out_parts: list[str] = []
        while i < len(text):
            if text.startswith(esc, i):
                if keep_count > 0:
                    out_parts.append(esc)
                    keep_count -= 1
                else:
                    out_parts.append(plain)
                i += len(esc)
            else:
                out_parts.append(text[i])
                i += 1
        return "".join(out_parts)

    out = formatted
    out = drop_extra(out, r"\[", "[", original.count(r"\["))
    out = drop_extra(out, r"\]", "]", original.count(r"\]"))
    return out


def extract_bullet_style(md: str) -> tuple[list[str], dict[str, str]]:
    try:
        tokens = MarkdownIt().parse(md)
    except Exception:
        return [], {}

    lines = md.split("\n")
    list_markers: list[str] = []
    list_stack: list[str] = []
    item_markers: dict[str, set[str]] = {}

    for tok in tokens:
        if tok.type == "bullet_list_open":
            marker = tok.markup if tok.markup in "-*+" else "-"
            list_markers.append(marker)
            list_stack.append("bullet")
            continue
        if tok.type == "ordered_list_open":
            list_stack.append("ordered")
            continue
        if tok.type in {"bullet_list_close", "ordered_list_close"}:
            if list_stack:
                list_stack.pop()
            continue
        if tok.type != "list_item_open" or tok.map is None or not list_stack:
            continue
        if list_stack[-1] != "bullet":
            continue
        line_idx = tok.map[0]
        if not (0 <= line_idx < len(lines)):
            continue
        m = LIST_ITEM_MARKER_RE.match(lines[line_idx])
        if not m:
            continue
        marker = m.group(3)
        body = m.group(5).strip()
        item_markers.setdefault(body, set()).add(marker)

    unique_item_markers = {
        body: next(iter(markers))
        for body, markers in item_markers.items()
        if body and len(markers) == 1
    }
    return list_markers, unique_item_markers


def replace_list_item_marker(line: str, marker: str) -> str:
    m = LIST_ITEM_MARKER_RE.match(line)
    if not m:
        return line
    return f"{m.group(1)}{m.group(2)}{marker}{m.group(4)}{m.group(5)}"


def preserve_bullet_markers(original: str, formatted: str) -> str:
    original_markers, original_item_markers = extract_bullet_style(original)
    if not original_markers:
        return formatted

    try:
        tokens = MarkdownIt().parse(formatted)
    except Exception:
        return formatted

    lines = formatted.split("\n")
    replacements: dict[int, str] = {}
    list_stack: list[tuple[str, str | None]] = []
    bullet_list_idx = 0

    for tok in tokens:
        if tok.type == "bullet_list_open":
            default_marker = tok.markup if tok.markup in "-*+" else "-"
            marker = (
                original_markers[bullet_list_idx]
                if bullet_list_idx < len(original_markers)
                else default_marker
            )
            bullet_list_idx += 1
            list_stack.append(("bullet", marker))
            continue
        if tok.type == "ordered_list_open":
            list_stack.append(("ordered", None))
            continue
        if tok.type in {"bullet_list_close", "ordered_list_close"}:
            if list_stack:
                list_stack.pop()
            continue
        if tok.type != "list_item_open":
            continue
        if not list_stack or tok.map is None:
            continue
        list_kind, marker = list_stack[-1]
        if list_kind != "bullet" or marker is None:
            continue
        line_idx = tok.map[0]
        if 0 <= line_idx < len(lines):
            line_match = LIST_ITEM_MARKER_RE.match(lines[line_idx])
            if not line_match:
                continue
            body = line_match.group(5).strip()
            replacements[line_idx] = original_item_markers.get(body, marker)

    changed = False
    for line_idx, marker in replacements.items():
        new_line = replace_list_item_marker(lines[line_idx], marker)
        if new_line != lines[line_idx]:
            lines[line_idx] = new_line
            changed = True

    return "\n".join(lines) if changed else formatted


def format_doc_inner(
    inner: str,
    indent: str,
    *,
    mdformat_options: dict[str, object],
    preserve_bullets: bool,
    mask_risky: bool,
) -> tuple[str, bool]:
    if not inner:
        return inner, False

    leading, core, trailing = split_outer_whitespace(inner)
    if not core.strip():
        return inner, False

    if "\n" in leading:
        core = strip_prefix_once(core, indent)
    if indent:
        core = core.replace("\n" + indent, "\n")

    core_to_format = core
    token_map: dict[str, str] = {}
    if mask_risky:
        core_to_format, token_map = mask_risky_fragments(core)

    formatted = mdformat.text(core_to_format, options=mdformat_options).rstrip("\n")
    if mask_risky:
        # In masked mode, original escaped brackets are hidden behind tokens.
        # Any remaining escaped brackets are therefore formatting artifacts.
        formatted = re.sub(r"\\+\[", "[", formatted)
        formatted = re.sub(r"\\+\]", "]", formatted)
        formatted = unmask_fragments(formatted, token_map)
    else:
        formatted = drop_new_escaped_brackets(core, formatted)
    if preserve_bullets:
        formatted = preserve_bullet_markers(core, formatted)

    if indent and "\n" in formatted:
        formatted = formatted.replace("\n", "\n" + indent)

    rebuilt = f"{leading}{formatted}{trailing}"
    return rebuilt, rebuilt != inner


def process_file(
    path: Path,
    write: bool,
    *,
    mdformat_options: dict[str, object],
    preserve_bullets: bool,
    mask_risky: bool,
) -> tuple[int, int]:
    with path.open("r", encoding="utf-8", newline="") as f:
        src = f.read()
    comments = find_doc_comments(src)
    if not comments:
        return 0, 0

    doc_total = 0
    doc_changed = 0
    out = src

    for comment in reversed(comments):
        # Comment delimiters are always 3 chars for `/--` and `/-!` and 2 chars for `-/`.
        inner_start = comment.start + 3
        inner_end = comment.end - 2
        inner = out[inner_start:inner_end]
        indent = line_indent_before(out, comment.start)

        new_inner, changed = format_doc_inner(
            inner,
            indent,
            mdformat_options=mdformat_options,
            preserve_bullets=preserve_bullets,
            mask_risky=mask_risky,
        )
        doc_total += 1
        if not changed:
            continue

        doc_changed += 1
        out = out[:inner_start] + new_inner + out[inner_end:]

    if write and out != src:
        with path.open("w", encoding="utf-8", newline="") as f:
            f.write(out)

    return doc_total, doc_changed


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", default=["Mathlib"], help="Lean file/dir roots to scan")
    parser.add_argument("--write", action="store_true", help="Write changes to disk")
    parser.add_argument("--limit", type=int, default=0, help="Only process first N Lean files")
    parser.add_argument("--verbose", action="store_true", help="Print per-file stats when changed")
    parser.add_argument(
        "--number",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Apply consecutive numbering to ordered lists (mdformat `number` option).",
    )
    parser.add_argument(
        "--preserve-bullets",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Preserve original bullet markers (`*`, `-`, `+`) list-by-list after formatting.",
    )
    parser.add_argument(
        "--mask-risky",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Mask risky markdown fragments (math, reference links, TeX escapes) before formatting.",
    )
    args = parser.parse_args()

    paths = [Path(p) for p in args.paths]
    files = iter_lean_files(paths)
    if args.limit > 0:
        files = files[: args.limit]

    files_changed = 0
    docs_total = 0
    docs_changed = 0

    mdformat_options: dict[str, object] = {"number": args.number}

    for idx, path in enumerate(files, start=1):
        total, changed = process_file(
            path,
            write=args.write,
            mdformat_options=mdformat_options,
            preserve_bullets=args.preserve_bullets,
            mask_risky=args.mask_risky,
        )
        docs_total += total
        docs_changed += changed
        if changed > 0:
            files_changed += 1
            if args.verbose:
                print(f"{path}: changed {changed}/{total} doc comments")
        if idx % 500 == 0:
            print(f"Processed {idx}/{len(files)} files...", file=sys.stderr)

    mode = "write" if args.write else "dry-run"
    print(f"Mode: {mode}")
    print(f"Files scanned: {len(files)}")
    print(f"Files changed: {files_changed}")
    print(f"Doc comments scanned: {docs_total}")
    print(f"Doc comments changed: {docs_changed}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
