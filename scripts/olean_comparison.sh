#!/usr/bin/env bash

oleansDir=.lake/build/lib/Mathlib
# should be master
branch=adomani/CI_olean_size

du "${oleansDir}"

printf '\n\nCompare to master\n\n'

## retrieve the job id of the latest master run
jobID="$(curl https://github.com/leanprover-community/mathlib4/actions/workflows/build.yml?query=branch%3A"${branch}+is%3Asuccess" |
  sed -n 's=.*actions/runs/\([0-9]*\).*=\1=p' | head -1)"
printf $'Latest successful `%s`\'s job: %s\n' "${branch}" "${jobID}"

getCacheSize () { du "${oleansDir}" | sed "s=^=${1} =; s=\t= =g" ; }

# Because the `lean-pr-testing-NNNN` branches use toolchains that are "updated in place"
# the cache mechanism is unreliable, so we don't test it if we are on such a branch.
if [[ ! $(cat lean-toolchain) =~ ^leanprover/lean4-pr-releases:pr-release-[0-9]+$ ]]; then
  echo "* Get master's oleans"
  masterOleans="$(gh run view "${jobID}" --log |
    awk -F'\t' '
      /compare oleans/ { last=$NF; sub(/[^ ]* /, "", last); printf("master %s\n", last) }
      /Compare to master/ { exit 0 }')"
  printf 'Found oleans:\n%s\n' "$(echo "${masterOleans}" | head)"
  echo "* Get branch's oleans"
  newOleans="$(getCacheSize branch)"
  printf '%s\n%s\n' "${masterOleans}" "${newOleans}" |
    awk 'function format(percent,diff,fname) {
      return sprintf("| %4.2f%% | %s | %s |\n", percent, diff, fname)
    }
    BEGIN{
      pctBound=5
      printf("oleans folders whose size differs by more than %s%% from the corresponding master'"'"'s oleans.\nThe whole oleans folder is always reported.\n\n", pctBound) }
      { gsub(/\.lake\/build\/lib\//, "") }
      /master/ { size[$3]=$2; difference[$3]-=$2 }
      /branch/ { if(size[$3] == "") {size[$3]=$2} difference[$3]+=+$2 }
    END {
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
fi
