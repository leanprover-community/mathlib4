#!/usr/bin/env bash

 : <<'BASH_MODULE_DOCS'
`scripts/import_trans_difference.sh <opt_commit1> <opt_commit2>` outputs a full diff of the
change of transitive imports in all the files between `<opt_commit1>` and `<opt_commit2>`.

If the commits are not provided, then it uses the current commit as `commit1` and
current `master` as `commit2`.

The output is of the form

|Files     |Import difference|
|-         |-                |
|Mathlib...| -34             |
  ...
|Mathlib...| 579             |

with collapsible tabs for file entries with at least 3 files.
BASH_MODULE_DOCS

if [ -n "${1}" ]
then
  commit1="${1}"
else
  commit1="$(git rev-parse HEAD)"
fi

if [ -n "${2}" ]
then
  commit2="${2}"
else
  commit2="$(git merge-base master ${commit1})"
fi

#printf 'commit1: %s\ncommit2: %s\n' "$commit1" "$commit2"

currCommit="$(git rev-parse HEAD)"

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

printf '\n\n<details><summary>Import changes for all files</summary>\n\n%s\n\n</details>\n' "$(
  printf "|Files|Import difference|\n|-|-|\n"
  (awk -F, '{ diff[$1]+=$2 } END {
    con=0
    for(fil in diff) {
      if(!(diff[fil] == 0)) {
        con++
        nums[diff[fil]]++
        reds[diff[fil]]=reds[diff[fil]]" `"fil"`"
      }
    }
    if (200 <= con) { printf("Too many changes (%s)!\n", con) } else {
      for(x in reds) {
        if (nums[x] <= 2) { printf("|%s|%s|\n", reds[x], x) }
        else { printf("|<details><summary>%s files</summary>%s</details>|%s|\n", nums[x], reds[x], x) }
      }
    }
  }' transImports*.txt | sort -t'|' -n -k3
  ))"
