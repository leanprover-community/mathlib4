#!/usr/bin/env bash

commit1="$(git rev-parse HEAD)"
commit2="$(git merge-base master ${commit1})"
echo "$commit1 $commit2"

currCommit=star_real

getTransImports () {
  python3 scripts/count-trans-deps.py Mathlib |
    # produce lines of the form `Mathlib.ModelTheory.Algebra.Ring.Basic,-582`
    sed 's=\([0-9]*\)[},]=,'"${1}"'\1\n=g' |
    tr -d ' "{}:'
}

git checkout "${commit1}"
git checkout master scripts/count-trans-deps.py
getTransImports > transImports1.txt
git checkout "${currCommit}"

git checkout "${commit2}"
git checkout master scripts/count-trans-deps.py
getTransImports - > transImports2.txt
git checkout "${currCommit}"

printf '\n\n<details><summary>All import changes</summary>%s</details>\n' "$(
  printf "|Files|Import difference|\n|-|-|\n"
  (awk -F, '{ diff[$1]+=$2 } END {
    for(fil in diff) {
      if(!(diff[fil] == 0)) {
        nums[diff[fil]]++
        reds[diff[fil]]=reds[diff[fil]]" `"fil"`"
      }
    }
    for(x in reds) {
      if (nums[x] <= 2) { printf("|%s|%s|\n", reds[x], x) }
      else { printf("|<details><summary>%s files</summary>%s</details>|%s|\n", nums[x], reds[x], x) }
    }
  #  for(fil in diff) {
  #    if (!(diff[fil] == 0)) {
  #      printf("|%s|%s|\n", fil, diff[fil])
  #    }
  #  }
  }' transImports*.txt | sort -t'|' -n -k3
  ))"
