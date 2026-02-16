#!/usr/bin/env bash

# The line length limit of each file
limit=1500

# takes as input
# * a comma-separated list of headers, i.e. `"Lines,File"` and
# * a file/stdin input;
# returns an md-style table, introducing an empty line to separate long files from short ones.
# The file/stdin is expected to consist of space-separated entries.
mkMDtable () {
  awk -v limit="${limit}" -v heads="${1}" '
    function mkRow(m,str)
    { printf("|")
      for(i=1; i<=m; i++) {printf("%s|", str)}
      print "" }
    BEGIN{
      longTotal=0
      foundShort=0
      n=split(heads, headers, ",")
      printf("### The 10 longest files in `mathlib`\n\n")
      # mkRow, with the header entries
      printf("|")
      for(i=1; i<=n; i++) {printf(" %s |", headers[i])}
      print ""
      mkRow(n, "-")
    } (limit < $1+0) {longTotal++}
      ((foundShort == "0") && (0 < longTotal) && ($1+0 <= limit) && ($1+0 == $1)) {mkRow(n, " "); foundShort=1}
      # mkRow, with the entries of each line
      { printf("|")
        for(i=1; i<=n; i++) { printf(" %s |", $i) }
        print "" } END{
        if(longTotal == "0")
        { printf("\nAll files are within the length limit!\n") }
        else
        { printf("\n%s file%s exceed%s the length limit (%s).\n", longTotal, (longTotal == 1) ? "" : "s", (longTotal == 1) ? "s" : "", limit) }
    }' "${2}"
}

git ls-files 'Mathlib/*.lean' | # list the git-managed `Mathlib/` lean files
  tr -d "'" |                   # remove `'`, otherwise `xargs`` complains
  xargs wc -l --total=never |   # count lines, do not report totals
  sort -nr -k1 |                # numerical reverse sort of the first entry
  head -10 |                    # keep the first 10 lines
  sed 's=\(Mathlib[^ ]*\)\.lean=file#\1=' | # linkify the filenames
  mkMDtable "Lines,File"        # format into an md-table

printf '\nRef commit: [%s](https://github.com/leanprover-community/mathlib4/tree/%s)\n' "$(git rev-parse --short HEAD)" "$(git rev-parse HEAD)"
