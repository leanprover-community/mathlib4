#!/usr/bin/env python3
"""
Replace module-like references in comments/docstrings with explicit file paths.

Example transformation:
    `Data.Set.Basic` -> `Mathlib/Data/Set/Basic.lean`

By default this script runs in dry-run mode and reports proposed changes.
Use --apply to rewrite files in place.
"""
from __future__ import annotations

import argparse
import pathlib
import re
from typing import Dict, Iterable, Iterator, List, Tuple


DEFAULT_ROOTS = ["Mathlib", "Archive", "Counterexamples", "MathlibTest", "docs"]
BLOCK_COMMENT_START = "/-"
BLOCK_COMMENT_END = "-/"
LINE_COMMENT = "--"
TOKEN_RE = re.compile(r"(?<![A-Za-z0-9_])([A-Z][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)+)")


def iter_block_comment_segments(lines: Iterable[str]) -> Iterator[Tuple[int, str, str]]:
    """
    Yield (lineno, prefix, comment_text) for each line that is inside a comment.

    This keeps track of block comments so interior lines without explicit markers
    are still processed.
    """
    in_block = False
    for lineno, line in enumerate(lines, 1):
        comment = None
        prefix = ""

        if in_block:
            comment = line
            end_idx = line.find(BLOCK_COMMENT_END)
            if end_idx != -1:
                in_block = False
        else:
            line_idx = line.find(LINE_COMMENT)
            block_idx = line.find(BLOCK_COMMENT_START)
            idx = -1
            marker_len = 0
            if line_idx != -1 and (block_idx == -1 or line_idx < block_idx):
                idx = line_idx
                marker_len = len(LINE_COMMENT)
            elif block_idx != -1:
                idx = block_idx
                marker_len = len(BLOCK_COMMENT_START)
                # Track that we are inside a block comment if it doesn't end here.
                after = line[idx + marker_len :]
                if BLOCK_COMMENT_END not in after:
                    in_block = True
            if idx != -1:
                prefix = line[: idx + marker_len]
                comment = line[idx + marker_len :]

        if comment is not None:
            yield lineno, prefix, comment


def build_module_set(mathlib_root: pathlib.Path) -> set[str]:
    """Collect module names (with and without the `Mathlib.` prefix)."""
    modules: set[str] = set()
    for path in mathlib_root.rglob("*.lean"):
        rel = path.relative_to(mathlib_root).with_suffix("")
        mod = ".".join(rel.parts)
        modules.add(mod)
        modules.add(f"Mathlib.{mod}")
    return modules


def build_module_maps(roots: List[str]) -> Dict[str, Dict[str, pathlib.Path]]:
    """
    Build a mapping from module name to path for each root, and a combined map.

    Returns a dict containing:
      - "combined": module -> path (across all roots, preferring earlier roots)
      - per-root entries: root name -> module -> path
    """
    combined: Dict[str, pathlib.Path] = {}
    per_root: Dict[str, Dict[str, pathlib.Path]] = {}
    for root in roots:
        base = pathlib.Path(root)
        if not base.exists():
            continue
        mm: Dict[str, pathlib.Path] = {}
        for path in base.rglob("*.lean"):
            rel = path.relative_to(base).with_suffix("")
            mod = ".".join(rel.parts)
            mm[mod] = path
            mm[f"{root}.{mod}"] = path
        per_root[root] = mm
        # prefer earlier roots if collision
        for k, v in mm.items():
            combined.setdefault(k, v)
    per_root["combined"] = combined
    return per_root


def resolve_token(
    token: str, module_maps: Dict[str, Dict[str, pathlib.Path]], primary_root: str
) -> pathlib.Path | None:
    """
    Resolve a token to a path.

    If the token is explicitly prefixed with a known root (e.g. `Archive.Foo`),
    only that root is considered. Otherwise we use the primary root (default: Mathlib).
    """
    # Explicit root prefix
    for root in module_maps:
        if root == "combined":
            continue
        if token.startswith(f"{root}."):
            return module_maps[root].get(token)

    # Unprefixed: prefer primary root
    primary_map = module_maps.get(primary_root, {})
    return primary_map.get(token)


def replace_tokens(
    text: str, module_maps: Dict[str, Dict[str, pathlib.Path]], primary_root: str
) -> Tuple[str, list[str]]:
    """Replace module tokens in the given text, returning new text and hits."""
    hits: list[str] = []

    def _replacement(match: re.Match[str]) -> str:
        token = match.group(1)
        path = resolve_token(token, module_maps, primary_root)
        if path is None:
            return token
        hits.append(token)
        rel = path.as_posix()
        return rel

    return TOKEN_RE.sub(_replacement, text), hits


def find_files(roots: list[str]) -> Iterator[pathlib.Path]:
    for root in roots:
        base = pathlib.Path(root)
        if not base.exists():
            continue
        yield from base.rglob("*.lean")


def process_file(
    path: pathlib.Path, module_maps: Dict[str, Dict[str, pathlib.Path]], primary_root: str, apply: bool
) -> list[str]:
    lines = path.read_text(encoding="utf-8").splitlines()
    changes: list[str] = []
    new_lines = lines[:]

    for lineno, prefix, comment in iter_block_comment_segments(lines):
        # Ignore commented-out imports to avoid rewriting them.
        if "import" in comment:
            continue
        new_comment, hits = replace_tokens(comment, module_maps, primary_root)
        if not hits or new_comment == comment:
            continue
        new_lines[lineno - 1] = f"{prefix}{new_comment}"
        for token in hits:
            resolved = resolve_token(token, module_maps, primary_root)
            if resolved is None:
                continue
            changes.append(f"{path}:{lineno}: {token} -> {resolved.as_posix()}")

    if apply and changes:
        path.write_text("\n".join(new_lines) + "\n", encoding="utf-8")

    return changes


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--apply",
        action="store_true",
        help="Rewrite files in place (default: dry-run).",
    )
    parser.add_argument(
        "--roots",
        nargs="*",
        default=DEFAULT_ROOTS,
        help="Root directories to scan for modules and files (default: %(default)s). Earlier roots win on conflicts.",
    )
    args = parser.parse_args()

    module_maps = build_module_maps(args.roots)
    primary_root = args.roots[0] if args.roots else "Mathlib"
    all_changes: list[str] = []

    for path in find_files(args.roots):
        all_changes.extend(process_file(path, module_maps, primary_root, args.apply))

    if not all_changes:
        print("No replacements found.")
        return

    print("Planned replacements:" if not args.apply else "Applied replacements:")
    for line in all_changes:
        print(line)


if __name__ == "__main__":
    main()
