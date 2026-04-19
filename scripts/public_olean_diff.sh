#!/usr/bin/env bash
# Compare the public `.olean` files of two Mathlib builds.
#
# In the module system, each module produces three olean files:
#   Foo.olean          -- public/exported information (signatures, axioms)
#   Foo.olean.server   -- docstrings, declaration ranges
#   Foo.olean.private  -- full private data including proof bodies
#
# Theorems are exported as axioms in the public `.olean`, so changing only
# a proof body should leave the public `.olean` byte-identical. This script
# compares the public oleans only, skipping `.olean.private`, `.olean.server`,
# and `.ir.olean`.
#
# Usage:
#   public_olean_diff.sh <base_lib_dir> <head_lib_dir> <output_file>
#
# Arguments:
#   base_lib_dir   path to `.lake/build/lib/lean` for the base (e.g. master)
#   head_lib_dir   path to `.lake/build/lib/lean` for the PR
#   output_file    path where the list of differing modules will be written
#
# Exit codes:
#   0  the public oleans are byte-identical for every module present in both builds
#   1  one or more public oleans differ
#   2  argument error or missing directories
#
# The output file contains one line per module whose public olean differs,
# in the form `Mathlib/Foo/Bar.olean`. An empty file means "no differences".
# Modules present in only one of the two builds are also listed (prefixed
# with `added: ` or `removed: `).

set -euo pipefail

if [ "$#" -ne 3 ]; then
  echo "usage: $0 <base_lib_dir> <head_lib_dir> <output_file>" >&2
  exit 2
fi

BASE_DIR="$1"
HEAD_DIR="$2"
OUT="$3"

if [ ! -d "$BASE_DIR" ]; then
  echo "error: base lib dir does not exist: $BASE_DIR" >&2
  exit 2
fi
if [ ! -d "$HEAD_DIR" ]; then
  echo "error: head lib dir does not exist: $HEAD_DIR" >&2
  exit 2
fi

# List public oleans (relative paths) in a directory. We include `*.olean`
# but exclude the `.olean.private`, `.olean.server`, and `.ir.olean`
# companions. `find -name '*.olean'` with a negative pattern keeps this
# simple and robust against file-name variations.
list_public_oleans() {
  local dir="$1"
  ( cd "$dir" && find . -type f -name '*.olean' \
      ! -name '*.olean.private' \
      ! -name '*.olean.server' \
      ! -name '*.ir.olean' \
      -printf '%P\n' | LC_ALL=C sort )
}

BASE_LIST="$(mktemp)"
HEAD_LIST="$(mktemp)"
trap 'rm -f "$BASE_LIST" "$HEAD_LIST"' EXIT

list_public_oleans "$BASE_DIR" > "$BASE_LIST"
list_public_oleans "$HEAD_DIR" > "$HEAD_LIST"

: > "$OUT"
differ=0

# Modules removed in the head build (present in base but not in head).
while IFS= read -r f; do
  echo "removed: $f" >> "$OUT"
  differ=1
done < <(comm -23 "$BASE_LIST" "$HEAD_LIST")

# Modules added in the head build (present in head but not in base).
while IFS= read -r f; do
  echo "added: $f" >> "$OUT"
  differ=1
done < <(comm -13 "$BASE_LIST" "$HEAD_LIST")

# Modules present in both: compare byte-by-byte.
while IFS= read -r f; do
  if ! cmp -s "$BASE_DIR/$f" "$HEAD_DIR/$f"; then
    echo "$f" >> "$OUT"
    differ=1
  fi
done < <(comm -12 "$BASE_LIST" "$HEAD_LIST")

if [ "$differ" -eq 0 ]; then
  echo "public_olean_diff: no public olean differences"
  exit 0
else
  echo "public_olean_diff: $(wc -l < "$OUT") public olean(s) differ"
  exit 1
fi
