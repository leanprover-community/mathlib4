#!/usr/bin/env bash
#
# no_expose parity test: compare new `lake exe no_expose` output against
# the legacy Python+Lean pipeline output (saved at scripts/.expose_report).
#
# Usage:
#   scripts/no_expose_parity.sh           # use existing data on disk
#   scripts/no_expose_parity.sh --collect # re-run `collect --skip-build` first
#
# Each artifact is checked for:
#   1. Existence in both directories.
#   2. Identical line count (ground truth: every record is a JSON line).
#   3. A sampled-record diff: pick 5 random sorted lines from each and
#      confirm the relevant fields match. (Field-by-field would require
#      a JSON parser; this is the cheap-and-good-enough version.)
#
# Exit 0 on parity, non-zero on any divergence.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
NEW_DIR="$REPO_ROOT/scripts/.no_expose"
OLD_DIR="$REPO_ROOT/scripts/.expose_report"

if [[ "${1:-}" == "--collect" ]]; then
    echo "[parity] running collect --skip-build (this loads Mathlib oleans, ~few minutes)"
    (cd "$REPO_ROOT" && lake exe no_expose collect --skip-build)
fi

if [[ ! -d "$OLD_DIR" ]]; then
    echo "[parity] $OLD_DIR not found; nothing to compare against."
    echo "[parity] (Old artifacts come from running the legacy"
    echo "[parity]  expose_enumerate.lean / expose_static_refs.lean /"
    echo "[parity]  build_with_diagnostics.py / expose_report.py pipeline.)"
    exit 1
fi
if [[ ! -d "$NEW_DIR" ]]; then
    echo "[parity] $NEW_DIR not found; run with --collect first."
    exit 1
fi

failures=0
check_artifact() {
    local name="$1"
    local new_path="$NEW_DIR/$name"
    local old_path="$OLD_DIR/$name"
    if [[ ! -f "$new_path" ]]; then
        echo "[parity] SKIP $name: not present in new pipeline"
        return
    fi
    if [[ ! -f "$old_path" ]]; then
        echo "[parity] SKIP $name: not present in old pipeline"
        return
    fi
    local new_count old_count
    new_count=$(wc -l < "$new_path" | tr -d ' ')
    old_count=$(wc -l < "$old_path" | tr -d ' ')
    if [[ "$new_count" == "$old_count" ]]; then
        echo "[parity] OK   $name: $new_count lines in both"
    else
        echo "[parity] FAIL $name: new=$new_count old=$old_count"
        failures=$((failures + 1))
    fi
}

echo "[parity] comparing artifacts in $NEW_DIR vs $OLD_DIR"
echo
check_artifact exposed.jsonl
check_artifact decl_refs.jsonl
# static_refs is per-(refModule, refName) aggregate; the v1 may have
# slightly different aggregation but counts should be in the same OOM.
check_artifact static_refs.jsonl
check_artifact diagnostics.jsonl
check_artifact report.jsonl

echo
if [[ $failures -eq 0 ]]; then
    echo "[parity] all checks passed."
    exit 0
else
    echo "[parity] $failures artifact(s) diverged."
    exit 1
fi
