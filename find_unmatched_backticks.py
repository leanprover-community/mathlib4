#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path
import bisect
import textwrap

ROOT = Path('.')
OUT_PATH = ROOT / 'unmatched_backticks_report.txt'
SUFFIXES = {'.lean'}
ALLOWED_PREFIXES = (
    'Mathlib/',
    'Archive/',
    'Counterexamples/',
    'docs/',
    'MathlibTest/',
    'LongestPole/',
    'README',
)

def _allowed(rel: str) -> bool:
    return any(rel.startswith(prefix) for prefix in ALLOWED_PREFIXES)


def _has_unmatched_backticks(body: str) -> bool:
    """Return True if `body` contains an unmatched Markdown backtick delimiter."""
    open_delim: int | None = None
    i = 0
    n = len(body)
    while i < n:
        if body[i] != '`':
            i += 1
            continue
        j = i + 1
        while j < n and body[j] == '`':
            j += 1
        run_len = j - i
        if open_delim is None:
            open_delim = run_len
        elif run_len == open_delim:
            open_delim = None
        else:
            # Backticks inside a code span that don't match the opening delimiter
            # are literal text, so we ignore them.
            pass
        i = j
    return open_delim is not None


def main() -> None:
    results: list[tuple[str, int, int, str]] = []
    for path in sorted(ROOT.rglob('*')):
        if not path.is_file() or path.suffix not in SUFFIXES:
            continue
        rel = path.relative_to(ROOT).as_posix()
        if not _allowed(rel):
            continue
        try:
            text = path.read_text()
        except UnicodeDecodeError:
            text = path.read_text(errors='ignore')
        line_starts = [0]
        for idx, ch in enumerate(text):
            if ch == '\n':
                line_starts.append(idx + 1)
        i = 0
        n = len(text)
        in_string = False
        while i < n:
            ch = text[i]
            if in_string:
                if ch == '\\' and i + 1 < n:
                    i += 2
                    continue
                if ch == '"':
                    in_string = False
                i += 1
                continue
            if ch == '"':
                in_string = True
                i += 1
                continue
            if text.startswith('--', i):
                newline = text.find('\n', i)
                if newline == -1:
                    break
                i = newline + 1
                continue
            if text.startswith('/-', i):
                start_idx = i
                is_doc = text.startswith('/--', i) or text.startswith('/-!', i)
                i += 2
                depth = 1
                while i < n and depth > 0:
                    if text.startswith('/-', i):
                        depth += 1
                        i += 2
                    elif text.startswith('-/', i):
                        depth -= 1
                        i += 2
                    else:
                        i += 1
                if not is_doc:
                    continue
                body = text[start_idx:min(i, n)]
                tick_count = body.count('`')
                if _has_unmatched_backticks(body):
                    line_no = bisect.bisect_right(line_starts, start_idx)
                    snippet = ' '.join(body.splitlines()).replace('\t', ' ')
                    snippet = textwrap.shorten(snippet, width=160, placeholder='...')
                    results.append((rel, line_no, tick_count, snippet))
                continue
            i += 1

    with OUT_PATH.open('w', encoding='utf-8') as fh:
        if not results:
            fh.write('No doc comments with unmatched backtick delimiters found.\n')
        else:
            fh.write(f'Found {len(results)} doc comments with unmatched backtick delimiters.\n')
            for rel, line_no, tick_count, snippet in results:
                fh.write(
                    f"{rel}:{line_no}: block doc comment has {tick_count} ` characters "
                    "and appears to have unmatched delimiters.\n"
                )
                fh.write(f"    {snippet}\n")

if __name__ == '__main__':
    main()
