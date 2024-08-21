#!/usr/bin/env bash

getCacheSize () {
  >&2 lake exe cache get
  du .lake/build/lib/Mathlib | sed "s=^=${1} =; s=\t= =g"
}

# Because the `lean-pr-testing-NNNN` branches use toolchains that are "updated in place"
# the cache mechanism is unreliable, so we don't test it if we are on such a branch.
if [[ ! $(cat lean-toolchain) =~ ^leanprover/lean4-pr-releases:pr-release-[0-9]+$ ]]; then
  mv .lake .lakeBranch
  git fetch origin master --depth 1
  git checkout origin/master
  masterOleans="$(getCacheSize master)"
  git checkout -
  mv -f .lakeBranch .lake
  newOleans="$(getCacheSize branch)"
  pctgs="$(printf '%s\n%s\n' "${masterOleans}" "${newOleans}" |
    awk 'function format(percent,diff,fname) {
      return sprintf("| %4.2f%% | %s | %s |\n", percent, diff, fname)
    }
    BEGIN{ pctBound=5 }
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
    }
    ')"
  printf '%s\n' "${pctgs}"
  printf '%s\n' "${pctgs}" >> "${GITHUB_OUTPUT}"
  #printf '.lake size\nmaster: %s\nthis PR: %s' "${masterOleans}" "${newOleans}"
fi
