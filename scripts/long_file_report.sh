#!/usr/bin/env bash

# takes a comma-separated list of headers and a file/stdin input and returns
# a md-style table. The file/stdin is expected to be space-separated entries.
mkMDtable () {
  awk -v limit=1500 -v heads="${1}" 'BEGIN{
    longTotal=0
    n=split(heads, headers, ",")
    printf("|")
    for(i=1; i<=n; i++) {printf(" %s |", headers[i])}
    print ""

    printf("|")
    for(i=1; i<=n; i++) {printf("-|")}
    print ""
  } ((longTotal == "0") && ($1+0 <= limit)) {longTotal=1; print "here"}
    {
    printf("|")
    for(i=1; i<=n; i++) {printf(" %s |", $i)}
    print ""
  } END{if(longTotal == "0") {printf("All files are within the length limit!\n")}{printf("There are long files.\n")}}' "${2}"
}

git ls-files 'Mathlib/*.lean' | # list the git-managed `Mathlib/` lean files
  tr -d "'" |                   # remove `'`, otherwise `xargs`` complains
  xargs wc -l --total=never |   # count lines, do not report totals
  sort -nr -k1 |                # numerical reverse sort of the first entry
  head -10 |                    # keep the first 10 lines
  sed 's=\(Mathlib[^ ]*\)\.lean=file#\1=' | # linkify the filenames
  mkMDtable "Lines,File"        # format into an md-table

printf '\nRef commit: [%s](https://github.com/leanprover-community/mathlib4/tree/%s)\n' "$(git rev-parse --short HEAD)" "$(git rev-parse HEAD)"
