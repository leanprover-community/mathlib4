#!/usr/bin/env bash
# declsDiff.sh — given two pre-computed declarations dumps (decls.txt files
# produced by `dumpReasonableDecls.lean`), produce:
#   * the raw `+NAME` / `-NAME` diff (sorted by NAME),
#   * a Markdown override snippet ready for mathlib-ci's `build_summary_body.sh`
#     to splice into the `#### Declarations diff` section.
#
# This script does NO env loading, NO cache operations, NO worktrees — it
# just compares two pre-existing text files. The expensive work
# (`withImportModules`) has already happened in each commit's Build job and
# the results are downloaded from CI artifacts.
#
# Inputs:
#   --ref-decls FILE       declarations dump of the reference commit
#   --new-decls FILE       declarations dump of the new commit
#   --new-sha SHA          full SHA of the new commit (for the stamp)
#
# Outputs (any combination):
#   --decls-override FILE  Markdown override snippet (no `#### Declarations diff`
#                            heading, no outer <details> wrap — both are added
#                            by build_summary_body.sh based on length)
#   --diff-out FILE        raw +/- lines (one entry per line)
#   --counts-file FILE     "<plus> <minus>\n"
#
# Misc:
#   --script-path PATH     path to `dumpReasonableDecls.lean` (for --diff
#                            mode, which is the only Lean call we make).
#                            Default: ../dumpReasonableDecls.lean relative
#                            to this script.
#   -h, --help

set -euo pipefail

REF_DECLS=""
NEW_DECLS=""
NEW_SHA=""
DECLS_OVERRIDE=""
DIFF_OUT=""
COUNTS_FILE=""
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN_SCRIPT="$HERE/dumpReasonableDecls.lean"

while [ $# -gt 0 ]; do
  case "$1" in
    --ref-decls)         REF_DECLS="$2";       shift 2 ;;
    --ref-decls=*)       REF_DECLS="${1#*=}";   shift   ;;
    --new-decls)         NEW_DECLS="$2";       shift 2 ;;
    --new-decls=*)       NEW_DECLS="${1#*=}";   shift   ;;
    --new-sha)           NEW_SHA="$2";         shift 2 ;;
    --new-sha=*)         NEW_SHA="${1#*=}";     shift   ;;
    --decls-override)    DECLS_OVERRIDE="$2";  shift 2 ;;
    --decls-override=*)  DECLS_OVERRIDE="${1#*=}"; shift ;;
    --diff-out)          DIFF_OUT="$2";        shift 2 ;;
    --diff-out=*)        DIFF_OUT="${1#*=}";    shift   ;;
    --counts-file)       COUNTS_FILE="$2";     shift 2 ;;
    --counts-file=*)     COUNTS_FILE="${1#*=}"; shift   ;;
    --script-path)       LEAN_SCRIPT="$2";     shift 2 ;;
    --script-path=*)     LEAN_SCRIPT="${1#*=}"; shift   ;;
    -h|--help)
      sed -n '2,35p' "$0" | sed 's/^# \{0,1\}//'
      exit 0 ;;
    *)
      echo "declsDiff.sh: unknown argument: $1" >&2
      exit 2 ;;
  esac
done

if [ ! -s "$REF_DECLS" ]; then
  echo "declsDiff.sh: --ref-decls is missing or empty: '$REF_DECLS'" >&2
  exit 1
fi
if [ ! -s "$NEW_DECLS" ]; then
  echo "declsDiff.sh: --new-decls is missing or empty: '$NEW_DECLS'" >&2
  exit 1
fi
if [ ! -f "$LEAN_SCRIPT" ]; then
  echo "declsDiff.sh: Lean script not found: '$LEAN_SCRIPT'" >&2
  exit 1
fi

WORK="$(mktemp -d -t declsDiff.XXXXXX)"
trap "rm -rf '$WORK'" EXIT INT TERM

# Compute the diff via the Lean script's --diff mode. This is pure file I/O
# (set difference of two sorted name lists); no env load.
DIFF="$WORK/diff.txt"
lake env lean --run "$LEAN_SCRIPT" \
  --diff "$NEW_DECLS" "$REF_DECLS" --out="$DIFF" >&2

PLUS="$(grep -c '^+' "$DIFF" 2>/dev/null || true)"
MINUS="$(grep -c '^-' "$DIFF" 2>/dev/null || true)"
: "${PLUS:=0}"; : "${MINUS:=0}"
SHORT_SHA="${NEW_SHA:0:7}"

# Render the override snippet. NO heading and NO outer details wrap — the
# body builder in mathlib-ci adds those based on content length (matching
# the existing `declarations_diff.sh` formatting heuristic).
if [ -n "$DECLS_OVERRIDE" ]; then
  TOTAL="$(wc -l < "$DIFF" | tr -d ' ')"
  {
    if [ -n "$SHORT_SHA" ]; then
      printf '> ✅ **Lean-aware diff** — post-build, computed from the Lean environment (commit `%s`).\n' \
        "$SHORT_SHA"
    else
      printf '> ✅ **Lean-aware diff** — post-build, computed from the Lean environment.\n'
    fi
    printf '\n'
    printf '* **+%s** new declarations\n' "$PLUS"
    printf '* **−%s** removed declarations\n' "$MINUS"
    if [ "${PLUS}${MINUS}" = "00" ]; then
      printf '\n_No declaration differences._\n'
    else
      printf '\n'
      if [ "$TOTAL" -gt 200 ]; then
        printf '_(showing first 200 of %s lines)_\n\n' "$TOTAL"
      fi
      printf '```diff\n'
      head -200 "$DIFF"
      printf '```\n'
    fi
  } > "$DECLS_OVERRIDE"
fi

if [ -n "$DIFF_OUT" ]; then
  cp "$DIFF" "$DIFF_OUT"
fi

if [ -n "$COUNTS_FILE" ]; then
  printf '%s %s\n' "$PLUS" "$MINUS" > "$COUNTS_FILE"
fi
