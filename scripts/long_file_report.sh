#!/usr/bin/env bash

# takes a comma-separated list of headers and a file/stdin input and returns
# a md-style table. The file/stdin is expected to be space-separated entries.
mkMDtable () {
  awk -v heads="${1}" 'BEGIN{
    n=split(heads, headers, ",")
    printf("|")
    for(i=1; i<=n; i++) {printf(" %s |", headers[i])}
    print ""

    printf("|")
    for(i=1; i<=n; i++) {printf("-|")}
    print ""
  } {
    printf("|")
    for(i=1; i<=n; i++) {printf(" %s |", $i)}
    print ""
  }' "${2}"
}

git ls-files 'Mathlib/*.lean' | # list the git-managed `Mathlib/` lean files
  tr -d "'" |                   # remove `'`, otherwise `xargs`` complains
  xargs wc -l --total=never |   # count lines, do not report totals
  sort -nr -k1 |                # numerical reverse sort of the first entry
  head -10 |                    # keep the first 10 lines
  sed 's=\(Mathlib[^ ]*\)\.lean=file#\1=' | # linkify the filenames
  mkMDtable "Lines,File"        # format into an md-table
