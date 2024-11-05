#!/usr/bin/env bash

# TODO
# If a merged PR touched one of the files in the most recent report, trigger the workflow again.
# Show the diff relative to the last report. (Using zulip/github as the persistent state?)

# `root` is the module name that the script builds
root=${1:-Mathlib}

# `lineLimit` is the number of module names of output that the script returns
# a value of `0` means that all files are returned
lineLimit=${2:-0}

# `significantDifference` is the threshold difference in imports above which
# the script reports the module
significantDifference=${3:-0}

jobID="${4}"

>&2 printf $'Building \'%s\'\n' "${root}"
>&2 printf $'Report only the top \'%s\' exceptions\n' "${lineLimit}"
>&2 printf $'Consider a file an exception if the last import increase exceeds \'%s\' imports\n\n' "${significantDifference}"
>&2 printf $'GitHub job id: \'%s\'\n\n' "${jobID}"

#baseURL='https://github.com/leanprover-community/mathlib4/commit'
baseURL='https://github.com/leanprover-community/mathlib4'
refCommit="$(git rev-parse HEAD)" #${{ github.sha }}

# build the selected target and collapse all `linter.minImports` warning to a single line per warning
lake build "${root}" | sed -z 's=\n\n*\([^⚠w]\)= \1=g' |
  # the `gsub`s clear all unnecessary text, leaving lines of the form
  # `warning: [filename]:[line]:[column]:[importIncrease]: [newImports]`
  # in awk-speak, $2=[filename], $3=[line], $5=[importIncrease], $6=[newImports]
  awk -F: 'BEGIN{max=0}
    # only print `currMax` when we reach the report for the next file (are we missing the last report?)
    /^⚠/{ print currMax; max=0 }
    (max < $3) {
      gsub(/ *Now redun.*/, "")
      gsub(/ to \[[^]]*\]/, "")
      gsub(/ *note: this linter.*/, "")
      gsub(/\.\//, "")
      gsub(/ *Imports increased by */, "")
      gsub(/ *New imports */, "")
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
      con=0
  }
    ((con <= lineLimit) && (significantDifference <= $5+0)) {
      if (!(lineLimit == 0)) { con++ }
      fileHtml=$2
      gsub(/\.lean$/, ".html", fileHtml)
      gsub(/ /, "", fileHtml)
      printf("| [%s](https://leanprover-community.github.io/mathlib4_docs/%s) | %s | %s | %s |\n", $2, fileHtml, $3, $5, $6)
  }'
printf '\n\n---\n\nReference commit [%s](%s)\n' "${refCommit:0:10}" "${baseURL}/commit/${refCommit}"
printf '[Full report](%s/actions/runs/%s)\n' "${baseURL}" "${jobID}"
