#!/usr/bin/env bash

 : << 'BASH_MODULE_DOCS'

This is the main script for the `compare oleans` CI step.
It should take place after `lake build` has taken place, since it computes sizes of the oleans.

First, the script first prints the sizes of the oleans of the *current* branch.
This means that on a PR you see the sizes of the newly created oleans
and on master you see the sizes of the "comparison" oleans.

Next, the script retrieves the sizes from master (using the printout from the previous step in
the logs of the latest CI run on master).

Finally, the script runs the comparison between the two sizes, flagging every folder that had a
percentage change of at least 5% (either positive or negative).
The percentage difference for the full oleans folder is always printed, whether or not it exceeds
the threshold.

BASH_MODULE_DOCS

# Because the `lean-pr-testing-NNNN` branches use toolchains that are "updated in place"
# the cache mechanism is unreliable, so we don't test it if we are on such a branch.
if [[ $(cat lean-toolchain) =~ ^leanprover/lean4-pr-releases:pr-release-[0-9]+$ ]]; then
  printf 'No summary, since this is a pr testing branch\n'
fi

oleansDir=.lake/build/lib/Mathlib

# should be master
branch=test/CI_olean_size

# This string separates the printout of the oleans from their analysis
separatorMessage='Compare to master'

# the absolute difference, in %, that is significant for a folder being reported
pctBound=5

# print the sizes
du "${oleansDir}"

printf '\n\n%s\n\n' "${separatorMessage}"

## retrieve the job id of the latest master run -- could not find a good way to do it with `gh run list`
jobID="$(curl --silent --show-error https://github.com/leanprover-community/mathlib4/actions/workflows/build.yml?query=branch%3A"${branch}+is%3Asuccess" |
  sed -n 's=.*actions/runs/\([0-9]*\).*=\1=p' | head -1)"
printf $'Job ID of the latest successful build on `%s`: %s\n' "${branch}" "${jobID}"

## retrieve master's oleans by looking at the beginning of the
## log for the `compare oleans` job on master
## (also append `master ` at the beginning of each row)
masterOleans="$(gh run view "${jobID}" --log |
  awk -v sep="${separatorMessage}" 'BEGIN{ stop=0 }
    ($0 ~ sep) { stop=1 }
    ((stop == 0) && /compare oleans.*lake/) {
      printf("master %s %s\n", $(NF-1), $NF)
    }')"

## `getCacheSize txt` tallies the sizes of the oleans, adding `txt` at the start of each line
## used to separate `master` and `branch` data.
getCacheSize () { du "${oleansDir}" | sed "s=^=${1} =; s=\t= =g" ; }
newOleans="$(getCacheSize branch)"
## print both tallies, compare values and report a summary
printf '%s\n%s\n' "${masterOleans}" "${newOleans}" |
  awk -v pctBound="${pctBound}" 'function format(percent,diff,fname) {
    return sprintf("| %4.2f%% | %s | %s |\n", percent, diff, fname)
  }
  BEGIN{
    printf("**\nFolders whose size differs by more than %s%% from the corresponding master'"'"'s oleans.\nThe whole oleans folder is always reported.\n**\n\n", pctBound) }
    { gsub(/\.lake\/build\/lib\//, "") }
    # size accumulates the absolute value of the folder sizes, using `master`s size if available
    # difference accumulates `branch size - master size`
    /master/ { size[$3]=$2; difference[$3]-=$2 }
    /branch/ { if(size[$3] == "") {size[$3]=$2} difference[$3]+=$2 }
  END {
    # final tally, the `Mathlib` folder is isolated and put at the bottom, no matter what
    printf("| %% | Difference | Folder |\n| -: | -: | - |\n")
    for(fil in difference) {
      pct=100*difference[fil]/size[fil]
      if (fil ~ /Mathlib$/) {
        mathlib=format(pct, difference[fil], fil)
      } else {
        if((pct <= -pctBound) || ((pctBound <= pct)))
        { print format(pct, difference[fil], fil) }
      }
    }
    print mathlib
  }'
