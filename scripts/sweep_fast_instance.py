#!/usr/bin/env python3
"""sweep_fast_instance.py

Wrap mathlib instance bodies whose RHS uses a known smart constructor with
`fast_instance%`. Keep the edit only if the file still builds *and* the
`linter.fast_instance_existing` warning does not fire.

Usage:
    # dry run over a subtree, just report candidates
    python3 sweep_fast_instance.py --dry-run Mathlib/Algebra/Order

    # really edit and verify, single file
    python3 sweep_fast_instance.py Mathlib/Algebra/Order/Monoid/Basic.lean

    # parallel sweep
    python3 sweep_fast_instance.py -j8 Mathlib

Run from the mathlib repo root.
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

# ---------------------------------------------------------------------------
# Patterns
# ---------------------------------------------------------------------------

# Smart-constructor names observed in existing `fast_instance%` uses across
# mathlib. Misses are fine — they simply won't be auto-swept.
SMART = re.compile(
    r"""\b(
        Function\.Injective\.\w+
      | Function\.Surjective\.\w+
      | \w+\.coe_injective\.\w+              # DFunLike / SetLike-style
      | \w+\.(induced|lift|copy|compHom)     # NormedGroup.induced, PartialOrder.lift, ...
      | Equiv\.\w+
      | \w+\.ofMinimalAxioms
      | \w+\.ofCoreReplaceAll
      | Fintype\.ofEquiv
      | Quotient\.mk
      | Denumerable\.mk
    )\b""",
    re.VERBOSE,
)

# Anchor at the `instance` keyword at line start; everything past it is parsed
# in Python to avoid regex backtracking on multi-line declarations.
INSTANCE_HEAD = re.compile(
    r"(?m)^(?P<indent>[ \t]*)(?:noncomputable[ \t]+)?instance\b"
)

# Messages that mean: revert the edit. Each is a warning lake prints when
# `fast_instance%` is inappropriate (linter, or Prop-class case from FastInstance.lean).
BAD_MESSAGES = (
    "Please use `inferInstance` instead of `fast_instance%`",
    "is a proof, which does not need normalization",
)

UNKNOWN_FAST_INSTANCE = "Unknown identifier `fast_instance`"

# Body prefixes for which `fast_instance%` is either redundant or unhelpful.
_BAD_BODY_PREFIXES = (
    "fast_instance%",
    "inferInstanceAs%",
    "inferInstanceAs",
    "inferInstance",
    "{",
)

# ---------------------------------------------------------------------------
# Edit logic
# ---------------------------------------------------------------------------

def _skip_comment(text: str, j: int) -> int | None:
    """If position j starts a comment, return position right after it; else None."""
    if text.startswith("--", j):
        nl = text.find("\n", j)
        return len(text) if nl < 0 else nl
    if text.startswith("/-", j):
        end = text.find("-/", j + 2)
        return len(text) if end < 0 else end + 2
    return None


def _find_body(text: str, after_kw: int, head_indent: int):
    """Starting just past an `instance` keyword, find the body. Returns
    (body_start, body_end) or None to skip (e.g. `where` block, no `:=`)."""
    n = len(text)
    depth = 0
    j = after_kw
    while j < n:
        skip = _skip_comment(text, j)
        if skip is not None:
            j = skip
            continue
        c = text[j]
        if c in "([{":
            depth += 1
            j += 1
            continue
        if c in ")]}":
            depth -= 1
            j += 1
            continue
        if depth == 0:
            if text.startswith(":=", j):
                body_start = j + 2
                while body_start < n and text[body_start] in " \t":
                    body_start += 1
                if body_start < n and text[body_start] == "\n":
                    body_start += 1
                    while body_start < n and text[body_start] in " \t":
                        body_start += 1
                body_end = body_start
                while body_end < n:
                    nl = text.find("\n", body_end)
                    if nl < 0:
                        body_end = n
                        break
                    line_start = nl + 1
                    col = 0
                    while line_start + col < n and text[line_start + col] in " \t":
                        col += 1
                    if line_start + col >= n or text[line_start + col] == "\n":
                        body_end = nl
                        break
                    if col <= head_indent:
                        body_end = nl
                        break
                    body_end = nl + 1
                return body_start, body_end
            if (text.startswith("where", j)
                    and (j + 5 >= n
                         or not (text[j + 5].isalnum() or text[j + 5] == "_"))):
                return None
            if c == "\n":
                line_start = j + 1
                col = 0
                while line_start + col < n and text[line_start + col] in " \t":
                    col += 1
                if (line_start + col < n
                        and text[line_start + col] != "\n"
                        and col <= head_indent):
                    return None
        j += 1
    return None


def candidate_edits(text: str) -> list[tuple[int, int, str]]:
    """Return [(start, end, replacement), ...] for instance declarations whose
    body looks like a smart-constructor application."""
    out: list[tuple[int, int, str]] = []
    pos = 0
    while True:
        m = INSTANCE_HEAD.search(text, pos)
        if m is None:
            break
        head_indent = len(m.group("indent"))
        found = _find_body(text, m.end(), head_indent)
        if found is None:
            pos = m.end()
            continue
        body_start, body_end = found
        body = text[body_start:body_end]
        body_stripped = body.lstrip()
        if (body_stripped.startswith(_BAD_BODY_PREFIXES)
                or body_stripped.startswith("by ")
                or body_stripped.startswith("by\n")
                or body_stripped.rstrip() == "by"):
            pos = body_end
            continue
        if SMART.search(body) is None:
            pos = body_end
            continue
        trimmed = body.rstrip()
        repl = "fast_instance% " + trimmed
        out.append((body_start, body_start + len(trimmed), repl))
        pos = body_end
    return out


def apply_edits(text: str, edits: list[tuple[int, int, str]],
                picked: set[int]) -> str:
    """Apply the subset of edits given by `picked` (indices into `edits`)."""
    out, off = text, 0
    for i, (s, e, r) in enumerate(edits):
        if i not in picked:
            continue
        out = out[: s + off] + r + out[e + off :]
        off += len(r) - (e - s)
    return out


# ---------------------------------------------------------------------------
# Build / verify
# ---------------------------------------------------------------------------

def build(file: Path, repo_root: Path) -> tuple[bool, str]:
    """Elaborate `file` using cached deps. Returns (success, combined output)."""
    r = subprocess.run(
        ["lake", "env", "lean", str(file)],
        capture_output=True, text=True, cwd=repo_root,
    )
    return r.returncode == 0, r.stdout + r.stderr


def edit_ok(file: Path, text: str, repo_root: Path) -> bool:
    file.write_text(text)
    ok, log = build(file, repo_root)
    if not ok:
        return False
    return all(msg not in log for msg in BAD_MESSAGES)


_IMPORT_RE = re.compile(r"(?m)^(?:public\s+)?import\s+\S+[ \t]*$")
_MODULE_RE = re.compile(r"(?m)^module[ \t]*$")


def add_fast_instance_import(text: str) -> str:
    """If `Mathlib.Tactic.FastInstance` isn't imported, add it after the last
    existing import. Returns original text if no `import` lines exist or the
    import is already present."""
    if "Mathlib.Tactic.FastInstance" in text:
        return text
    last = None
    for m in _IMPORT_RE.finditer(text):
        last = m
    if last is None:
        return text
    is_module = bool(_MODULE_RE.search(text[:last.end()]))
    line = ("public import Mathlib.Tactic.FastInstance"
            if is_module else "import Mathlib.Tactic.FastInstance")
    return text[:last.end()] + "\n" + line + text[last.end():]


# ---------------------------------------------------------------------------
# Per-file sweep
# ---------------------------------------------------------------------------

def sweep(file: Path, repo_root: Path, dry_run: bool) -> tuple[int, int]:
    """Return (n_candidates, n_kept). On dry-run, n_kept == 0 and nothing changes."""
    orig = file.read_text()
    edits = candidate_edits(orig)
    if not edits:
        return 0, 0
    if dry_run:
        return len(edits), 0

    # Probe: is `fast_instance%` available in this file's import closure?
    file.write_text(apply_edits(orig, edits, {0}))
    _, probe_log = build(file, repo_root)
    if UNKNOWN_FAST_INSTANCE in probe_log:
        new_orig = add_fast_instance_import(orig)
        if new_orig == orig:
            file.write_text(orig); build(file, repo_root)
            return len(edits), 0
        base = new_orig
        edits = candidate_edits(base)  # re-scan: offsets shift after import line
        if not edits:
            file.write_text(orig); build(file, repo_root)
            return 0, 0
    else:
        base = orig

    pool = set(range(len(edits)))

    if edit_ok(file, apply_edits(base, edits, pool), repo_root):
        return len(edits), len(pool)

    # Fallback: incrementally accumulate compatible edits.
    kept: set[int] = set()
    for i in range(len(edits)):
        if edit_ok(file, apply_edits(base, edits, kept | {i}), repo_root):
            kept.add(i)
    if kept:
        file.write_text(apply_edits(base, edits, kept))
    else:
        file.write_text(orig)
    build(file, repo_root)
    return len(edits), len(kept)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def find_files(roots: list[str]) -> list[Path]:
    files: list[Path] = []
    for r in roots:
        p = Path(r)
        if p.is_file() and p.suffix == ".lean":
            files.append(p)
        else:
            files.extend(p.rglob("*.lean"))
    # Prefilter: only files that have at least one candidate. Keeps the worker
    # pool from spawning useless rebuilds.
    return [f for f in files if candidate_edits(f.read_text())]


def _worker(args):
    file, repo_root, dry_run = args
    try:
        return file, sweep(file, repo_root, dry_run), None
    except Exception as e:
        return file, (0, 0), repr(e)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("paths", nargs="+", help="files or directories to sweep")
    ap.add_argument("-j", "--jobs", type=int, default=1,
                    help="parallel workers (default 1)")
    ap.add_argument("--dry-run", action="store_true",
                    help="report candidates without editing or building")
    args = ap.parse_args()

    repo_root = Path.cwd()
    if not (repo_root / "lakefile.lean").exists() \
       and not (repo_root / "lakefile.toml").exists():
        sys.exit("error: run from mathlib repo root (no lakefile here)")

    files = find_files(args.paths)
    print(f"# scanning {len(files)} candidate file(s)")
    total_cand = total_kept = 0

    work = [(f, repo_root, args.dry_run) for f in files]
    if args.jobs > 1 and not args.dry_run:
        with ProcessPoolExecutor(max_workers=args.jobs) as ex:
            for fut in as_completed([ex.submit(_worker, w) for w in work]):
                f, (n_cand, n_kept), err = fut.result()
                total_cand += n_cand
                total_kept += n_kept
                tag = "DRY " if args.dry_run else ""
                print(f"{tag}{f}: {n_kept}/{n_cand}" + (f"  ERR {err}" if err else ""))
    else:
        for w in work:
            f, (n_cand, n_kept), err = _worker(w)
            total_cand += n_cand
            total_kept += n_kept
            tag = "DRY " if args.dry_run else ""
            print(f"{tag}{f}: {n_kept}/{n_cand}" + (f"  ERR {err}" if err else ""))

    print(f"# total: kept {total_kept} / {total_cand} candidate edit(s) "
          f"across {len(files)} file(s)")


if __name__ == "__main__":
    main()
