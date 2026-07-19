#!/usr/bin/env python3
"""Re-wrap multi-line `[...]` tactic argument lists (rw/simp/grind/...) so that items
are packed greedily up to the 100-character limit.

Only ever *merges* lines (never splits), only touches bracket spans in tactic position
whose top-level comma-separated items each live on a single line, and never touches
spans that contain comments or that would not shrink.
"""

import argparse
import re
import sys
from pathlib import Path

MAX = 100

OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⟦": "⟧", "⦃": "⦄", "⟮": "⟯"}
CLOSE = {v: k for k, v in OPEN.items()}

# Only reflow bracket lists in tactic position. Term-level list literals (notably
# `List.TFAE [...]`) contain binder commas (`∃ l, ...`, `∀ ⦃x⦄, ...`) that read as
# top-level separators, so re-wrapping them splits mid-binder and looks wrong.
TACTICS = {
    "rw", "rewrite", "rwa", "erw", "grw", "nth_rw", "nth_rewrite",
    "simp", "simp_rw", "simp_all", "simpa", "dsimp", "only", "contextual",
    "norm_num", "field_simp", "push_cast", "norm_cast", "aesop", "grind",
    "gcongr", "positivity", "unfold", "filter_upwards", "exacts", "algebraize",
    "abel", "ring_nf", "linarith", "nlinarith", "polyrith", "fun_prop",
    "measurability", "continuity", "fin_cases", "interval_cases", "bound",
}

TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")


def in_tactic_position(text, oi):
    """True if the `[` at index oi is the argument list of a tactic."""
    toks = TOKEN_RE.findall(text[max(0, oi - 200):oi])
    return bool(toks) and toks[-1] in TACTICS


def scan(text):
    """Return (bracket_spans, mask).

    Spans are (open_idx, close_idx) for every `[` ... `]` pair, at any nesting depth.
    mask[i] is True if character i is inside a comment or string/char literal.
    """
    n = len(text)
    mask = bytearray(n)
    stack = []
    spans = []
    i = 0
    block_depth = 0
    while i < n:
        c = text[i]
        if block_depth:
            mask[i] = 1
            if text.startswith("/-", i):
                block_depth += 1
                mask[i + 1] = 1
                i += 2
                continue
            if text.startswith("-/", i):
                block_depth -= 1
                mask[i + 1] = 1
                i += 2
                continue
            i += 1
            continue
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                mask[k] = 1
            i = j
            continue
        if text.startswith("/-", i):
            block_depth = 1
            mask[i] = mask[i + 1] = 1
            i += 2
            continue
        if c == '"':
            j = i + 1
            mask[i] = 1
            while j < n:
                mask[j] = 1
                if text[j] == "\\":
                    if j + 1 < n:
                        mask[j + 1] = 1
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            i = j
            continue
        if c == "'" and i + 2 < n:
            j = i + 1
            if text[j] == "\\":
                j += 1
                while j < n and text[j] != "'":
                    j += 1
                j += 1
            else:
                j += 2
            if j <= n and "\n" not in text[i + 1 : j] and j - i <= 12 and text[j - 1] == "'":
                for k in range(i, j):
                    mask[k] = 1
                i = j
                continue
            i += 1
            continue
        if c in OPEN:
            stack.append((c, i))
        elif c in CLOSE:
            if stack and stack[-1][0] == CLOSE[c]:
                op, oi = stack.pop()
                if op == "[":
                    spans.append((oi, i))
            else:
                stack.clear()
        i += 1
    return spans, mask


def split_items(s):
    """Split a top-level comma-separated list. Returns None if unbalanced."""
    items = []
    depth = 0
    cur = 0
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c == '"':
            i += 1
            while i < n:
                if s[i] == "\\":
                    i += 2
                    continue
                if s[i] == '"':
                    break
                i += 1
        elif c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
            if depth < 0:
                return None
        elif c == "," and depth == 0:
            items.append(s[cur:i])
            cur = i + 1
        i += 1
    items.append(s[cur:])
    return items


def line_bounds(text, idx):
    start = text.rfind("\n", 0, idx) + 1
    end = text.find("\n", idx)
    return start, (len(text) if end < 0 else end)


def reflow_span(text, oi, ci):
    """Return (start, end, replacement) or None."""
    inner = text[oi + 1 : ci]
    if "\n" not in inner:
        return None
    if not in_tactic_position(text, oi):
        return None

    items = split_items(inner)
    if items is None or len(items) < 2:
        return None
    stripped = [it.strip() for it in items]
    if any(("\n" in it) or (it == "") for it in stripped):
        return None

    pstart, _ = line_bounds(text, oi)
    prefix = text[pstart : oi + 1]
    if prefix.lstrip().startswith("--"):
        return None
    _, lend = line_bounds(text, ci)
    tail = text[ci:lend]

    # continuation lines keep the file's existing indent (Lean is indent-sensitive)
    nl = text.find("\n", oi)
    cont_start, cont_end = line_bounds(text, nl + 1)
    cont_line = text[cont_start:cont_end]
    indent = cont_line[: len(cont_line) - len(cont_line.lstrip())]
    if indent.strip() != "":
        return None

    lines = []
    cur = prefix
    for k, it in enumerate(stripped):
        last = k == len(stripped) - 1
        piece = it if last else it + ","
        extra = tail if last else ""
        sep = "" if cur.endswith("[") else " "
        cand = cur + sep + piece + extra
        # break only when it helps: a fresh line must actually be shorter
        if cur.strip() and len(cand) > MAX and len(indent + piece + extra) < len(cand):
            lines.append(cur)
            cur = indent + piece
        else:
            cur = cur + sep + piece
    lines.append(cur + tail)

    new = "\n".join(lines)
    old = text[pstart:lend]
    if new == old or new.count("\n") >= old.count("\n"):
        return None
    return (pstart, lend, new)


def process(text):
    spans, mask = scan(text)
    spans.sort(key=lambda s: (s[0], -s[1]))  # outermost-first, left-to-right
    edits = []
    taken_end = -1
    for oi, ci in spans:
        if oi < taken_end or any(mask[oi:ci]):
            continue
        r = reflow_span(text, oi, ci)
        if r is None:
            continue
        edits.append(r)
        taken_end = r[1]

    if not edits:
        return text, 0
    out = []
    pos = 0
    for s, e, rep in edits:
        if s < pos:
            continue
        out.append(text[pos:s])
        out.append(rep)
        pos = e
    out.append(text[pos:])
    return "".join(out), len(edits)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()

    files = []
    for p in args.paths:
        p = Path(p)
        files.extend(sorted(p.rglob("*.lean")) if p.is_dir() else [p])

    total_edits = 0
    total_files = 0
    for f in files:
        text = f.read_text(encoding="utf-8")
        new, k = process(text)
        if k:
            total_edits += k
            total_files += 1
            if args.apply:
                f.write_text(new, encoding="utf-8")
            else:
                print(f"{f}: {k}")
    print(f"{total_edits} spans in {total_files} files", file=sys.stderr)


if __name__ == "__main__":
    main()
