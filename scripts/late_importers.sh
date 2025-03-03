#!/usr/bin/env bash

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

 : <<'BASH_MODULE_DOCS'

This script formats the `linter.minImports` output, returning a table of the form

| File           | Line | Import increase | New imports            |
| :-             | -:   | -:              | :-                     |
| Mathlib/X.lean | 1123 | 75              | [Mathlib.Y, Mathlib.Z] |

where the column
* `File` consists of doc-gen links,
* `Line` is the position of the last import bump in the file,
* `Import increase` is the number of extra imports implied by the last bump,
* `New imports` is the list of new imports needed for the last bump.

The table is sorted by descending order of `Line` column.

The script that takes 4 arguments:
1. the module name that should be built (`Mathlib` by default);
2. the number of module names of output that the script returns (all by default);
3. the threshold difference in imports above which the script reports a module (all by default);
4. the GitHub job-ID of the workflow run.

TODO
* If a merged PR touched one of the files in the most recent report, trigger the workflow again.
* Show the diff relative to the last report. (Using zulip/github as the persistent state?)

BASH_MODULE_DOCS

# `root` is the module name that the script builds
root=${1:-Mathlib}

# `lineLimit` is the number of module names of output that the script returns
# a value of `0` means that all files are returned
lineLimit=${2:-0}

# `significantDifference` is the threshold difference in imports above which
# the script reports the module
significantDifference=${3:-0}

jobID="${4:-N/A}"

>&2 printf $'Building \'%s\'\n' "${root}"
>&2 printf $'Report only the top \'%s\' exceptions\n' "${lineLimit}"
>&2 printf $'Consider a file an exception if the last import increase exceeds \'%s\' imports\n\n' "${significantDifference}"
>&2 printf $'GitHub job id: \'%s\'\n\n' "${jobID}"

baseURL='https://github.com/leanprover-community/mathlib4'
refCommit="$(git rev-parse HEAD)" #${{ github.sha }}

# build the selected target and collapse all `linter.minImports` warning to a single line per warning
lake build "${root}" | sed -z 's=\n\n*\([^⚠w]\)= \1=g' |
  # the `gsub`s clear all unnecessary text, leaving lines of the form
  # `warning:[filename]:[line]:[column]:[importIncrease]:[newImports]`
  # in awk-speak, $2=[filename], $3=[line], $5=[importIncrease], $6=[newImports]
  awk -F: 'BEGIN{max=0}
    # only print `currMax` when we reach the report for the next file (are we missing the last report?)
    /^⚠/{ print currMax; max=0 }
    (max < $3) {
      gsub(/ *Now redun.*/, "")
      gsub(/ to \[[^]]*\]/, "")
      gsub(/ *note: this linter.*/, "")
      gsub(/ *\.\//, "")
      gsub(/ *Imports increased by */, "")
      gsub(/ *New imports: */, ":")
      currMax=$0
      max=$3+0
  }' |
  # sort by decreasing line with the last import increase
  sort --field-separator=: -k3 -nr |
  # prepare the table in markdown format
  awk -F: -v lineLimit="${lineLimit}" -v significantDifference="${significantDifference}" '
    BEGIN{
      lineLimit=lineLimit+0
      significantDifference=significantDifference+0
      printf("| File | Line | Import increase | New imports |\n| :- | -: | -: | :- |\n")
      con=1
  }
    ( ((lineLimit == 0) || (con <= lineLimit)) && (significantDifference <= $5+0) ) {
      con++
      fileHtml=$2
      gsub(/\.lean$/, ".html", fileHtml)
      printf("| [%s](https://leanprover-community.github.io/mathlib4_docs/%s) | %s | %s | %s |\n", $2, fileHtml, $3, $5, $6)
  }' | column -s'|' -o'|' -t
printf '\n\n---\n\nReference commit [%s](%s)\n' "${refCommit:0:10}" "${baseURL}/commit/${refCommit}"
printf '[Full report](%s/actions/runs/%s)\n' "${baseURL}" "${jobID}"
