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

formatGitDiff () {
  git diff --name-status "${1}" |
    awk -F'\t' '!($1 == "M") {
      printf("%s,,%s%s\n", NF == 2? $2 : $3, $1, NF == 2? "" : ","$2)
    }' |
    sed '
      s=/=.=g
      s=\.lean,=,=
      s=,A=, (new file)=
      s=,D=, (removed file)=
      s=,R[0-9]*,\(.*\)=, (paired with `\1`)=
    '
}

getFormattedTransImports () {
  { getTransImports
    formatGitDiff "${1}"; } |
    awk -F, '
         ($2+0 == $2) { record[$1]=$2; #if(name[$1] == "")
           { name[$1]="`"$1"`" } }
         ($2 == "")   { name[$1]="`"$1"`"$3 }
      END {
        for(fil in name)
        { printf("%s,%s\n", name[fil], record[fil]) }
      }'
}

git checkout "${commit1}"
git checkout master scripts/count-trans-deps.py
getFormattedTransImports "${commit2}" > transImports1.txt
git checkout "${currCommit}"

git checkout "${commit2}"
git checkout master scripts/count-trans-deps.py
getFormattedTransImports "${commit1}" > transImports2.txt
git checkout "${currCommit}"

printf '\n\n<details><summary>Import changes for all files</summary>\n\n%s\n\n</details>\n' "$(
  printf "|Files|Import difference|\n|-|-|\n"
  (awk -F, '{ diff[$1]+=$2 } END {
    con=0
    for(fil in diff) {
      if(!(diff[fil] == 0)) {
        con++
        nums[diff[fil]]++
        reds[diff[fil]]=reds[diff[fil]]" "fil
      }
    }
    if (10000 <= con) { printf("There are %s files with changed transitive imports: this is too many to display!\n", con) } else {
      max=0
      for(x in reds) {
        max++
        #if(100 < max) { exit 1 }
        if (nums[x] <= 2) { printf("|%s|%s|\n", reds[x], x) }
        else { printf("|<details><summary>%s files</summary>%s</details>|%s|\n", nums[x], reds[x], x) }
      }
    }
  }' transImports*.txt | sort -t'|' -n -k3
  ))"

printf 'formatGitDiff %s\n' "${commit1}" &&
formatGitDiff "${commit1}" &&
printf 'formatGitDiff %s\n' "${commit2}" &&
formatGitDiff "${commit2}"
cat transImports1.txt
