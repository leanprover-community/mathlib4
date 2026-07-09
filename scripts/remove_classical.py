#!/usr/bin/env python3
"""Remove `classical` tactic uses that are not actually needed, verified by compiling.

For every occurrence of the `classical` tactic in every targeted file, tentatively
remove it and type-check the file with `lake env lean`. Removals that still compile
are recorded in a JSON journal; the file on disk is restored to its original content
as soon as its processing finishes, so the working tree stays clean during the run.
A separate `--apply` phase writes all journaled removals to disk in one batch.

Two syntactic forms are targeted:
  A. a line consisting solely of `classical` (deleted entirely). Lines with a
     trailing `--` comment (e.g. `classical -- needed for ...`) are left alone.
  B. inline `by classical` (rewritten to `by`), whether line-final or followed by
     more tactics on the same line.

Occurrences inside block comments and docstrings are never touched.

Usage:
  scripts/remove_classical.py Mathlib/MeasureTheory            # trial run, fills journal
  scripts/remove_classical.py Mathlib --resume --jobs 3        # continue a long run
  scripts/remove_classical.py --scan-only Mathlib              # list detected occurrences
  scripts/remove_classical.py --apply                          # write journaled removals
  scripts/remove_classical.py --self-test                      # scanner unit tests
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
JOURNAL_PATH = REPO_ROOT / "classical_removal_journal.json"

STANDALONE_RE = re.compile(r"^\s*classical\s*$")
INLINE_RE = re.compile(r"\bby classical(?=\s|$)")


@dataclass
class Occurrence:
    kind: str  # "line" (form A) or "inline" (form B)
    line: int  # 1-indexed
    col: int  # 0-indexed start of `by classical` for inline; 0 for line
    text: str  # original line content (without newline), for journal readability

    def key(self) -> tuple[int, int]:
        return (self.line, self.col)


def split_code(line: str, depth: int) -> tuple[str, int]:
    """Return (code part of the line, block-comment depth after the line).

    The code part has block-comment content, `--` line comments, and string
    literal content blanked out (replaced by spaces), so occurrence regexes only
    ever see real code. `depth` is the block-comment nesting depth at line start.
    """
    out = []
    i = 0
    n = len(line)
    in_string = False
    while i < n:
        if depth > 0:
            if line.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif line.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append(" ")
                i += 1
        elif in_string:
            if line[i] == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
            elif line[i] == '"':
                in_string = False
                out.append('"')
                i += 1
            else:
                out.append(" ")
                i += 1
        else:
            if line.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif line.startswith("--", i):
                out.append(" " * (n - i))
                break
            elif line[i] == '"':
                in_string = True
                out.append('"')
                i += 1
            else:
                out.append(line[i])
                i += 1
    return "".join(out), depth


def find_occurrences(lines: list[str]) -> list[Occurrence]:
    occs: list[Occurrence] = []
    depth = 0
    for lineno, raw in enumerate(lines, start=1):
        line = raw.rstrip("\n")
        started_in_comment = depth > 0
        code, depth = split_code(line, depth)
        if started_in_comment:
            continue
        if STANDALONE_RE.match(line):
            occs.append(Occurrence(kind="line", line=lineno, col=0, text=line))
            continue
        for m in INLINE_RE.finditer(code):
            occs.append(Occurrence(kind="inline", line=lineno, col=m.start(), text=line))
    return occs


def build_content(lines: list[str], occs: list[Occurrence], remove: set[tuple[int, int]]) -> str:
    by_line: dict[int, list[Occurrence]] = {}
    drop_lines: set[int] = set()
    for occ in occs:
        if occ.key() not in remove:
            continue
        if occ.kind == "line":
            drop_lines.add(occ.line)
        else:
            by_line.setdefault(occ.line, []).append(occ)

    out: list[str] = []
    for lineno, raw in enumerate(lines, start=1):
        if lineno in drop_lines:
            continue
        if lineno in by_line:
            for occ in sorted(by_line[lineno], key=lambda o: -o.col):
                raw = raw[: occ.col] + "by" + raw[occ.col + len("by classical") :]
        out.append(raw)
    return "".join(out)


def lake_env_lean(rel_path: str, timeout: float | None = None, lake_build: bool = False) -> tuple[bool, str]:
    if lake_build:
        module = ".".join(Path(rel_path).with_suffix("").parts)
        cmd = ["lake", "build", module]
    else:
        cmd = ["lake", "env", "lean", rel_path]
    try:
        result = subprocess.run(
            cmd,
            cwd=REPO_ROOT,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired:
        return False, "<timeout>"
    return result.returncode == 0, result.stdout + result.stderr


def process_file(rel_path: str, lake_build: bool = False) -> dict:
    """Trial-remove every occurrence in one file. Restores the file afterwards.

    Returns a journal entry dict.
    """
    path = REPO_ROOT / rel_path
    original = path.read_text()
    lines = original.splitlines(keepends=True)
    occs = find_occurrences(lines)
    entry: dict = {
        "sha256": hashlib.sha256(original.encode()).hexdigest(),
        "occurrences": [],
        "notes": [],
    }
    if not occs:
        entry["status"] = "no_occurrences"
        return entry

    start = time.monotonic()
    ok, baseline_output = lake_env_lean(rel_path, lake_build=lake_build)
    baseline_secs = time.monotonic() - start
    entry["baseline_seconds"] = round(baseline_secs, 1)
    if not ok:
        entry["status"] = "baseline_failed"
        entry["notes"].append(baseline_output[-2000:])
        return entry

    # In lake-build mode the baseline is a cached no-op, so its duration says
    # nothing about a real compile; use a generous fixed floor instead.
    timeout = max(10 * baseline_secs, baseline_secs + 120, 900 if lake_build else 0)
    accepted: set[tuple[int, int]] = set()
    try:
        for occ in occs:
            path.write_text(build_content(lines, occs, accepted | {occ.key()}))
            ok, output = lake_env_lean(rel_path, timeout=timeout, lake_build=lake_build)
            record = asdict(occ)
            record["removed"] = ok
            if ok:
                accepted.add(occ.key())
                if output.strip() != baseline_output.strip():
                    entry["notes"].append(
                        f"line {occ.line}: output changed after removal:\n{output[-1500:]}"
                    )
            entry["occurrences"].append(record)
    finally:
        path.write_text(original)

    entry["status"] = "done"
    return entry


def load_journal() -> dict:
    if JOURNAL_PATH.exists():
        return json.loads(JOURNAL_PATH.read_text())
    return {}


def save_journal(journal: dict) -> None:
    tmp = JOURNAL_PATH.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(journal, indent=1))
    tmp.replace(JOURNAL_PATH)


def is_excluded(path: Path) -> bool:
    rel_parts = path.relative_to(REPO_ROOT).parts
    return ".lake" in rel_parts or (rel_parts and rel_parts[0] == "MathlibTest")


def discover_files(args: list[str]) -> list[str]:
    files: set[Path] = set()
    for arg in args:
        root = Path(arg)
        if not root.is_absolute():
            root = REPO_ROOT / arg
        if not root.exists():
            raise FileNotFoundError(root)
        if root.is_file():
            if root.suffix == ".lean" and not is_excluded(root):
                files.add(root)
        else:
            files.update(p for p in root.rglob("*.lean") if not is_excluded(p))
    return sorted(str(p.relative_to(REPO_ROOT)) for p in files)


def apply_journal() -> int:
    journal = load_journal()
    applied_files = 0
    applied_occs = 0
    for rel_path, entry in sorted(journal.items()):
        removals = [o for o in entry.get("occurrences", []) if o.get("removed")]
        if entry.get("status") != "done" or not removals:
            continue
        path = REPO_ROOT / rel_path
        original = path.read_text()
        if hashlib.sha256(original.encode()).hexdigest() != entry["sha256"]:
            print(f"SKIP {rel_path}: file changed since it was scanned")
            continue
        lines = original.splitlines(keepends=True)
        occs = [Occurrence(o["kind"], o["line"], o["col"], o["text"]) for o in removals]
        path.write_text(build_content(lines, occs, {o.key() for o in occs}))
        applied_files += 1
        applied_occs += len(removals)
        print(f"{rel_path}: applied {len(removals)} removal(s)")
    print(f"\nApplied {applied_occs} removal(s) across {applied_files} file(s)")
    return 0


def scan_only(paths: list[str]) -> int:
    total = 0
    for rel_path in paths:
        lines = (REPO_ROOT / rel_path).read_text().splitlines(keepends=True)
        for occ in find_occurrences(lines):
            print(f"{rel_path}:{occ.line}:{occ.kind}: {occ.text.strip()}")
            total += 1
    print(f"\n{total} occurrence(s)", file=sys.stderr)
    return 0


SELF_TEST_SNIPPET = '''\
/-!
# Docstring header
A fake proof in a module docstring:
```
theorem foo : True := by
  classical
  trivial
```
-/

/- block comment
  classical
  /- nested
  classical
  -/
  classical
-/

/-- A docstring saying use `by classical` or
  classical
somewhere. -/
theorem real₁ : True := by
  classical
  trivial

theorem real₂ : True := by classical trivial

theorem real₃ : True := by classical
  trivial

theorem kept : True := by
  classical -- deliberate, do not remove
  trivial

def strfun : String := "by classical
  classical"

-- a line comment: classical
-- another: by classical here
theorem real₄ : True := by
    classical
  -- comment then code
'''


def self_test() -> int:
    lines = SELF_TEST_SNIPPET.splitlines(keepends=True)
    occs = find_occurrences(lines)
    got = {(o.kind, lines[o.line - 1].rstrip("\n").strip()) for o in occs}
    expected_texts = {
        ("line", "classical"),
        ("inline", "theorem real₂ : True := by classical trivial"),
        ("inline", "theorem real₃ : True := by classical"),
    }
    assert got == expected_texts, f"unexpected occurrence set: {got}"
    line_occs = [o for o in occs if o.kind == "line"]
    assert len(line_occs) == 2, f"expected 2 standalone occurrences, got {line_occs}"
    assert len(occs) == 4, f"expected 4 occurrences total, got {len(occs)}"

    # Removing everything must only delete/rewrite those exact sites.
    content = build_content(lines, occs, {o.key() for o in occs})
    assert "theorem real₂ : True := by trivial" in content
    assert "theorem real₃ : True := by\n  trivial" in content
    assert "classical -- deliberate, do not remove" in content
    assert content.count("classical") == SELF_TEST_SNIPPET.count("classical") - 4
    # Docstring/comment/string content untouched.
    for chunk in ["```\ntheorem foo", "/- block comment", 'def strfun : String := "by classical']:
        assert chunk in content

    # Removing nothing must reproduce the input exactly.
    assert build_content(lines, occs, set()) == SELF_TEST_SNIPPET

    # Partial removal: only real₂'s inline occurrence.
    inline2 = next(o for o in occs if o.kind == "inline" and "trivial" in o.text)
    partial = build_content(lines, occs, {inline2.key()})
    assert "theorem real₂ : True := by trivial" in partial
    assert "theorem real₃ : True := by classical" in partial
    assert partial.count("\n  classical\n") >= 1

    print("self-test OK")
    return 0


def run(paths: list[str], jobs: int, resume: bool, lake_build: bool = False) -> int:
    journal = load_journal()
    todo = []
    for rel_path in paths:
        if resume and rel_path in journal and journal[rel_path].get("status") in (
            "done",
            "no_occurrences",
        ):
            continue
        lines = (REPO_ROOT / rel_path).read_text().splitlines(keepends=True)
        n = len(find_occurrences(lines))
        if n:
            todo.append((rel_path, n))

    total_occs = sum(n for _, n in todo)
    print(f"{len(todo)} file(s) to process, {total_occs} occurrence(s), jobs={jobs}")
    start = time.monotonic()
    done_files = 0
    done_occs = 0
    removed_total = 0
    with concurrent.futures.ProcessPoolExecutor(max_workers=jobs) as pool:
        futures = {pool.submit(process_file, rel, lake_build): (rel, n) for rel, n in todo}
        for fut in concurrent.futures.as_completed(futures):
            rel_path, n = futures[fut]
            try:
                entry = fut.result()
            except Exception as e:  # noqa: BLE001 - record and continue the long run
                entry = {"status": "error", "notes": [repr(e)], "occurrences": []}
            journal[rel_path] = entry
            save_journal(journal)
            done_files += 1
            done_occs += n
            removed = sum(1 for o in entry.get("occurrences", []) if o.get("removed"))
            removed_total += removed
            elapsed = time.monotonic() - start
            eta = elapsed / done_occs * (total_occs - done_occs) if done_occs else 0
            print(
                f"[{done_files}/{len(todo)}] {rel_path}: {entry['status']}, "
                f"removed {removed}/{n} | total removed {removed_total} | "
                f"elapsed {elapsed / 60:.0f}m ETA {eta / 60:.0f}m",
                flush=True,
            )
    print(f"\nDone. Removable: {removed_total}/{done_occs} occurrence(s).")
    bad = [p for p, e in journal.items() if e.get("status") in ("baseline_failed", "error")]
    if bad:
        print(f"{len(bad)} file(s) with baseline failures/errors:")
        for p in bad:
            print(f"  {p}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paths", nargs="*", help="Lean files or directories to process")
    parser.add_argument("--jobs", type=int, default=3)
    parser.add_argument("--resume", action="store_true", help="skip files already in the journal")
    parser.add_argument("--apply", action="store_true", help="write journaled removals to disk")
    parser.add_argument("--scan-only", action="store_true", help="list occurrences, no compiling")
    parser.add_argument(
        "--lake-build",
        action="store_true",
        help="verify with `lake build <module>` instead of `lake env lean` (for files that "
        "fail standalone elaboration; requires a fully cached build, use --jobs 1)",
    )
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()

    if args.self_test:
        return self_test()
    if args.apply:
        return apply_journal()
    if not args.paths:
        parser.error("paths required (or --apply/--self-test)")
    paths = discover_files(args.paths)
    if args.scan_only:
        return scan_only(paths)
    return run(paths, jobs=args.jobs, resume=args.resume, lake_build=args.lake_build)


if __name__ == "__main__":
    sys.exit(main())
