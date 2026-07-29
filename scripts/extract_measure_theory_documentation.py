#!/usr/bin/env python3
"""Extract the comments in ``Mathlib/MeasureTheory`` into a plain-text corpus.

The resulting file is intended for prose-oriented tools such as spell checkers. It includes
ordinary Lean comments as well as declaration, module, and section documentation, except for
standard copyright headers.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import re
import sys
import textwrap


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SOURCE_ROOT = REPOSITORY_ROOT / "Mathlib" / "MeasureTheory"
DEFAULT_OUTPUT = REPOSITORY_ROOT / "docs" / "measure_theory_comments.txt"
BANNER = "=" * 80
QUALIFIED_IDENTIFIER = re.compile(r"(?:[A-Za-z_][A-Za-z0-9_']*\.)+[A-Za-z_][A-Za-z0-9_']*")
URL = re.compile(r"(?<![A-Za-z0-9_])(?:https?://|www\.)[^\s<>()]+")
AUTOLINK = re.compile(r"<(?:(?:https?://)|(?:www\.))[^>]+>")
FENCED_CODE_BLOCK = re.compile(r"(?ms)^[ \t]*```[^\n]*\n.*?^[ \t]*```[^\n]*(?:\n|$)")


@dataclass(frozen=True)
class Comment:
    """A comment's source range and its text without Lean delimiters."""

    start: int
    end: int
    text: str


def block_opener_length(source: str, start: int) -> int:
    """Return the length of a Lean block-comment opener at ``start``.

    ``/--`` and ``/-!`` are documentation variants, while all other block comments use ``/-``.
    The distinction matters only so that the punctuation is not emitted as prose.
    """

    if start + 2 < len(source) and source[start + 2] in "-!":
        return 3
    return 2


def skip_quoted_string(source: str, start: int) -> int:
    """Return the first index after a Lean string starting at ``start``.

    This handles ordinary, triple-quoted, and hash-delimited raw strings.  It deliberately
    tolerates an unterminated string: the rest of the source cannot contain comments then.
    """

    if source.startswith('"""', start):
        end = source.find('"""', start + 3)
        return len(source) if end == -1 else end + 3

    if source[start] == "r":
        match = re.match(r'r(?P<hashes>#*)"', source[start:])
        if match is not None:
            hashes = match.group("hashes")
            close = '"' + hashes
            end = source.find(close, start + len(match.group(0)))
            return len(source) if end == -1 else end + len(close)

    # Ordinary strings, including interpolated strings whose opening quote is preceded by `s!`.
    index = start + 1
    while index < len(source):
        if source[index] == "\\":
            index += 2
        elif source[index] == '"':
            return index + 1
        else:
            index += 1
    return len(source)


def read_block_comment(source: str, start: int) -> tuple[int, str]:
    """Read a nested Lean block comment and return its end index and delimiter-free text."""

    depth = 1
    index = start + block_opener_length(source, start)
    pieces: list[str] = []
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            index += block_opener_length(source, index)
        elif source.startswith("-/", index):
            depth -= 1
            index += 2
            if depth == 0:
                return index, "".join(pieces)
        else:
            pieces.append(source[index])
            index += 1
    raise ValueError("unterminated block comment")


def extract_comments(source: str) -> list[Comment]:
    """Extract all comments from Lean source, ignoring markers inside string literals."""

    comments: list[Comment] = []
    index = 0
    while index < len(source):
        if source.startswith("/-", index):
            end, text = read_block_comment(source, index)
            comments.append(Comment(index, end, text))
            index = end
        elif source.startswith("--", index):
            end = source.find("\n", index)
            if end == -1:
                end = len(source)
            comments.append(Comment(index, end, source[index + 2:end]))
            index = end
        elif source[index] == '"':
            index = skip_quoted_string(source, index)
        elif source[index] == "r" and re.match(r'r#*"', source[index:]):
            index = skip_quoted_string(source, index)
        else:
            index += 1
    return comments


def remove_code_spans(text: str) -> str:
    """Remove Markdown code spans and the remainder of lines with unmatched backticks."""

    text = FENCED_CODE_BLOCK.sub("", text)
    pieces: list[str] = []
    index = 0
    while index < len(text):
        if text[index] != "`":
            pieces.append(text[index])
            index += 1
            continue

        end_of_opener = index
        while end_of_opener < len(text) and text[end_of_opener] == "`":
            end_of_opener += 1
        delimiter = text[index:end_of_opener]
        close = text.find(delimiter, end_of_opener)
        line_end = text.find("\n", end_of_opener)
        if close == -1 or (line_end != -1 and close > line_end):
            # Lean comments occasionally contain malformed inline markup or metaprogramming
            # quotations. Since their contents are code rather than prose, discard the rest of
            # that line instead of leaking a backtick into the spelling corpus.
            index = len(text) if line_end == -1 else line_end
        else:
            index = close + len(delimiter)
    return "".join(pieces)


def clean_link_label(label: str) -> str:
    """Keep prose labels but discard qualified Lean identifiers used as cross-reference labels."""

    label = label.strip()
    return "" if QUALIFIED_IDENTIFIER.fullmatch(label) else label


def remove_links(text: str) -> str:
    """Remove Markdown link markup and destinations while retaining visible prose labels."""

    pieces: list[str] = []
    index = 0
    while index < len(text):
        if text[index] != "[":
            pieces.append(text[index])
            index += 1
            continue

        close_label = text.find("]", index + 1)
        if close_label == -1:
            pieces.append(text[index])
            index += 1
            continue

        label = clean_link_label(text[index + 1:close_label])
        target_start = close_label + 1
        if target_start < len(text) and text[target_start] == "(":
            depth = 1
            target_end = target_start + 1
            while target_end < len(text) and depth:
                if text[target_end] == "(":
                    depth += 1
                elif text[target_end] == ")":
                    depth -= 1
                target_end += 1
            if depth == 0:
                pieces.append(label)
                index = target_end
                continue
        elif target_start < len(text) and text[target_start] == "[":
            reference_end = text.find("]", target_start + 1)
            if reference_end != -1:
                pieces.append(label)
                index = reference_end + 1
                continue

        pieces.append(text[index])
        index += 1

    def remove_bare_url(match: re.Match[str]) -> str:
        # Sentence punctuation is not part of a bare URL, but the deliberately broad URL matcher
        # includes it so that a URL at the end of a sentence is removed in one pass.
        url = match.group(0)
        return url[len(url.rstrip(".,;:!?")):]

    return URL.sub(remove_bare_url, AUTOLINK.sub("", "".join(pieces)))


def clean_comment(text: str) -> str:
    """Turn one Lean comment into prose suitable for a typo-checking corpus."""

    text = remove_code_spans(text)
    text = remove_links(text)
    return textwrap.dedent(text).strip()


def is_copyright_header(text: str) -> bool:
    """Whether ``text`` is mathlib's standard per-file copyright header."""

    return "Copyright (c)" in text and "Released under Apache 2.0 license" in text


def display_path(path: Path, source_root: Path) -> str:
    """Return a stable, useful source name for a corpus file boundary."""

    try:
        return path.relative_to(REPOSITORY_ROOT).as_posix()
    except ValueError:
        return (Path(source_root.name) / path.relative_to(source_root)).as_posix()


def render_file(path: Path, source_root: Path) -> str:
    """Render one Lean file, including its boundary even when it has no surviving comments."""

    source = path.read_text(encoding="utf-8")
    comments = [(comment, clean_comment(comment.text)) for comment in extract_comments(source)]
    comments = [
        (comment, text)
        for comment, text in comments
        if text and not is_copyright_header(comment.text)
    ]

    body: list[str] = []
    previous_end: int | None = None
    for comment, text in comments:
        if previous_end is not None:
            gap = source[previous_end:comment.start]
            body.append(gap if gap.isspace() else "\n\n")
        body.append(text)
        previous_end = comment.end

    header = f"{BANNER}\nBEGIN FILE: {display_path(path, source_root)}\n{BANNER}"
    return header if not body else f"{header}\n\n{''.join(body).strip()}"


def build_corpus(source_root: Path) -> str:
    """Build the deterministic plain-text corpus for all Lean files below ``source_root``."""

    source_root = source_root.resolve()
    files = sorted(source_root.rglob("*.lean"), key=lambda path: path.as_posix())
    return "\n\n".join(render_file(path, source_root) for path in files) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--source-root",
        type=Path,
        default=DEFAULT_SOURCE_ROOT,
        help="directory containing MeasureTheory Lean files (default: %(default)s)",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help="generated corpus path (default: %(default)s)",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="fail if the output is missing or differs, without writing it",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    source_root = args.source_root.resolve()
    output = args.output.resolve()
    if not source_root.is_dir():
        print(f"source root does not exist: {source_root}", file=sys.stderr)
        return 2

    try:
        corpus = build_corpus(source_root)
    except ValueError as error:
        print(f"could not parse comments: {error}", file=sys.stderr)
        return 2

    if args.check:
        if not output.is_file() or output.read_text(encoding="utf-8") != corpus:
            print(f"{output} is stale; run {Path(__file__).name} to regenerate it", file=sys.stderr)
            return 1
        return 0

    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(corpus, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
