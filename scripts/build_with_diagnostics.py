#!/usr/bin/env python3
"""
Part of the `@[expose]` removal-candidate reporting pipeline
(see `scripts/expose_enumerate.lean` and `scripts/expose_report.py`).

Runs a full `lake build Mathlib` with `diagnostics=true` and
`diagnostics.threshold=0` enabled, captures per-file diagnostic output, and
emits one JSONL record per unfold event observed during elaboration.

Workflow:
  1. Patch `lakefile.lean` to append the diagnostics options to
     `mathlibLeanOptions` (this *does* affect the olean hash; a full local
     rebuild is expected).
  2. Run `lake build Mathlib`, streaming and teeing output to
     `scripts/.expose_report/build.log`.
  3. Parse the captured log into per-file unfold records.
  4. Emit `scripts/.expose_report/diagnostics.jsonl` — one record per
     (file, decl, category) triple.
  5. Restore `lakefile.lean` (always; even on failure / Ctrl-C).

Expected runtime: several hours for a full Mathlib rebuild with diagnostics.
Kim signed off on this cost: this is a one-off / occasional report.

Usage:
  python3 scripts/build_with_diagnostics.py
  python3 scripts/build_with_diagnostics.py --skip-build    # re-parse existing log
  python3 scripts/build_with_diagnostics.py --log PATH      # use alt log path

Output records:
  {
    "file":     "Mathlib/Foo/Bar.lean",
    "decl":     "Other.Module.name",
    "count":    3,
    "category": "reduction/unfolded" | "reduction/instances"
              | "reduction/reducible" | "kernel/unfolded"
  }

Limitations:
  * Signal is unfold-based; metaprograms that inspect `ConstantInfo.value?`
    without triggering a WHNF unfold don't appear here. A decl absent from
    this output may still be load-bearing downstream via metaprogramming.
  * `diagnostics.threshold` is set to `0`: every unfold appears in the
    report (counts > 0, since the threshold check is strictly-greater-than).
    A "never unfolded downstream" verdict means absence from the per-file
    diagnostic output — Lean does not emit zero-count rows. Un-exposure
    candidates should still be verified by trying the change and
    re-building, since metaprograms that inspect `ConstantInfo.value?`
    without a WHNF unfold won't appear here either.

    Note: low thresholds previously triggered
    https://github.com/leanprover/lean4/issues/13581 (private-helper
    rendering crash) on `nightly-2026-05-06` and earlier. Fixed by
    https://github.com/leanprover/lean4/pull/13630 (in
    `nightly-2026-05-07` and later).
"""

import argparse
import json
import os
import re
import shutil
import signal
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parent.parent
LAKEFILE = REPO_ROOT / "lakefile.lean"
OUTPUT_DIR = REPO_ROOT / "scripts" / ".expose_report"
DEFAULT_LOG = OUTPUT_DIR / "build.log"
DEFAULT_JSONL = OUTPUT_DIR / "diagnostics.jsonl"

PATCH_MARKER_BEGIN = "-- BEGIN expose_report diagnostics patch"
PATCH_MARKER_END = "-- END expose_report diagnostics patch"

# The extra LeanOptions lines inserted into `mathlibLeanOptions`.
PATCH_BLOCK = f"""    {PATCH_MARKER_BEGIN}
    ⟨`diagnostics, true⟩,
    ⟨`diagnostics.threshold, (0 : Nat)⟩,
    {PATCH_MARKER_END}
"""

# Insertion anchor inside `mathlibLeanOptions := #[ ... ]`. We insert *after*
# this line (which has no trailing comment, so preserving trailing text is
# not an issue).
ANCHOR = "    ⟨`autoImplicit, false⟩,\n"


def patch_lakefile() -> str:
    """Insert the diagnostics options into mathlibLeanOptions. Returns the
    original contents (for restoration)."""
    original = LAKEFILE.read_text()
    if PATCH_MARKER_BEGIN in original:
        raise RuntimeError(
            "lakefile.lean already contains expose_report patch markers; "
            "restore it manually before running again."
        )
    if ANCHOR not in original:
        raise RuntimeError(
            f"Could not find insertion anchor in lakefile.lean:\n  {ANCHOR!r}"
        )
    patched = original.replace(ANCHOR, ANCHOR + PATCH_BLOCK, 1)
    LAKEFILE.write_text(patched)
    return original


def restore_lakefile(original: str) -> None:
    LAKEFILE.write_text(original)


def run_build(log_path: Path) -> int:
    """Stream `lake build Mathlib` to stdout and to `log_path`. Returns exit."""
    log_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = ["lake", "build", "Mathlib"]
    print(f"[build_with_diagnostics] running: {' '.join(cmd)}", flush=True)
    with open(log_path, "w") as log:
        proc = subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT),
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
        assert proc.stdout is not None
        try:
            for line in proc.stdout:
                sys.stdout.write(line)
                sys.stdout.flush()
                log.write(line)
        except KeyboardInterrupt:
            proc.send_signal(signal.SIGINT)
            raise
        proc.wait()
        return proc.returncode


# --- log parsing --------------------------------------------------------

# Build-progress line: "✔ [N/M] Built Mathlib.Foo.Bar" or "ℹ [N/M] Built …"
# File attribution is driven entirely off this line: lake prints a file's
# info/trace/warning output immediately after its `Built` header, so the
# current-file cursor is unambiguous within a block.
BUILT_RE = re.compile(
    r"^[\u2714\u2139\u26A0\u2716]\s+\[\d+/\d+\]\s+Built\s+(\S+)"
)
# Header:  `  [reduction] unfolded declarations (max: N, num: M):`
CATEGORY_HEADER_RE = re.compile(
    r"^\s*\[(reduction|kernel)\]\s+(unfolded declarations|"
    r"unfolded instances|unfolded reducible declarations)\s*"
    r"\(max: \d+, num: \d+\):\s*$"
)
# Entry:   `    [reduction] Foo.bar ↦ 3`
ENTRY_RE = re.compile(
    r"^\s*\[(reduction|kernel)\]\s+(\S.*?)\s+↦\s+(\d+)\s*$"
)

CATEGORY_SHORT = {
    ("reduction", "unfolded declarations"): "reduction/unfolded",
    ("reduction", "unfolded instances"): "reduction/instances",
    ("reduction", "unfolded reducible declarations"): "reduction/reducible",
    ("kernel", "unfolded declarations"): "kernel/unfolded",
}


def target_to_file(target: str) -> str | None:
    """Convert `Mathlib.Foo.Bar` → `Mathlib/Foo/Bar.lean`. Non-file targets
    (those containing ':') return None."""
    if ":" in target:
        return None
    return target.replace(".", "/") + ".lean"


def parse_log(log_path: Path, out_path: Path) -> dict:
    """Parse `log_path` and write per-unfold JSONL records to `out_path`.
    Returns a summary dict."""
    out_path.parent.mkdir(parents=True, exist_ok=True)

    current_file: str | None = None
    current_category: str | None = None
    records_written = 0
    decls_seen: set[str] = set()
    files_seen: set[str] = set()

    with open(log_path) as log, open(out_path, "w") as out:
        for raw in log:
            line = raw.rstrip("\n")

            # 1. Update current-file context from the progress header.
            m = BUILT_RE.match(line)
            if m:
                current_file = target_to_file(m.group(1))
                current_category = None
                continue

            # 2. Diagnostic subcategory header.
            m = CATEGORY_HEADER_RE.match(line)
            if m:
                tag, label = m.group(1), m.group(2)
                current_category = CATEGORY_SHORT.get((tag, label))
                continue

            # 3. Entry line, only valid inside a known category and with a
            #    known current file.
            m = ENTRY_RE.match(line)
            if m and current_category is not None and current_file is not None:
                tag, decl, count = m.group(1), m.group(2), int(m.group(3))
                # The entry's tag should match the header's tag; if not, we
                # likely left the category silently. Reset and skip.
                if not current_category.startswith(tag):
                    current_category = None
                    continue
                record = {
                    "file": current_file,
                    "decl": decl,
                    "count": count,
                    "category": current_category,
                }
                out.write(json.dumps(record, separators=(",", ":")) + "\n")
                records_written += 1
                decls_seen.add(decl)
                files_seen.add(current_file)
                continue

            # 4. Any other non-entry line ends a category block.
            if line and not line.startswith(" "):
                current_category = None

    return {
        "records": records_written,
        "unique_decls": len(decls_seen),
        "files_with_diagnostics": len(files_seen),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--skip-build", action="store_true",
                    help="don't run lake build; parse existing log only")
    ap.add_argument("--log", type=Path, default=DEFAULT_LOG,
                    help=f"build log path (default: {DEFAULT_LOG})")
    ap.add_argument("--out", type=Path, default=DEFAULT_JSONL,
                    help=f"output JSONL path (default: {DEFAULT_JSONL})")
    args = ap.parse_args()

    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    rc = 0
    if not args.skip_build:
        original = patch_lakefile()
        try:
            rc = run_build(args.log)
        finally:
            restore_lakefile(original)
        if rc != 0:
            print(f"[build_with_diagnostics] lake build exited {rc}; "
                  f"log preserved at {args.log}. "
                  f"Re-run with --skip-build --log to reparse.",
                  file=sys.stderr)
            # Still parse: partial output is useful.

    if not args.log.exists():
        print(f"error: log not found: {args.log}", file=sys.stderr)
        return 2

    summary = parse_log(args.log, args.out)
    print(f"[build_with_diagnostics] wrote {summary['records']} records "
          f"({summary['unique_decls']} unique decls, "
          f"{summary['files_with_diagnostics']} files with diagnostics) "
          f"to {args.out}", file=sys.stderr)
    return rc


if __name__ == "__main__":
    sys.exit(main())
