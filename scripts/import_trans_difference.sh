#!/usr/bin/env bash

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

 : <<'BASH_MODULE_DOCS'
`scripts/import_trans_difference.sh <opt all> <opt_commit1> <opt_commit2>` outputs a full diff
of the change of transitive imports in all the files between `<opt_commit1>` and `<opt_commit2>`.

The optional flag `<opt all>` must either be `all` or not be passed.
Without `all`, the script only displays the difference if the output does not exceed 200 lines.

If the commits are not provided, then the script uses the current commit as `commit1` and
current `master` as `commit2`.

The output is of the form

|Files     |Import difference|
|-         |-                |
|Mathlib...| -34             |
  ...
|Mathlib...| 579             |

with collapsible tabs for file entries with at least 3 files.
BASH_MODULE_DOCS

# `all=1` is the flag to print all import changes, without cut-off
all=0
if [ "${1:-}" == "all" ]
then
  all=1
  shift
fi

commit1="${1:-"$(git rev-parse HEAD)"}"

commit2="${2:-"$(git merge-base master ${commit1})"}"

#printf 'commit1: %s\ncommit2: %s\n' "$commit1" "$commit2"

currCommit="$(git rev-parse --abbrev-ref HEAD)"
# if we are in a detached head, `currCommit` would be the unhelpful `HEAD`
# in this case, we fetch the commit hash
if [ "${currCommit}" == "HEAD" ]
then
  currCommit="$(git rev-parse HEAD)"
fi

getTransImports () {
  python3 scripts/count-trans-deps.py Mathlib |
    # produce lines of the form `Mathlib.ModelTheory.Algebra.Ring.Basic,-582`
    sed 's=\([0-9]*\)[},]=,'"${1:-}"'\1\n=g' |
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
  (gawk -F, -v all="${all}" -v ghLimit='261752' -v newFiles="$(
      # we pass the "A"dded files with respect to master, converting them to module names
      git diff --name-only --diff-filter=A master | tr '\n' , | sed 's=\.lean,=,=g; s=/=.=g'
    )" '
    BEGIN{
      # `arrayNewModules` maps integers to module names
      split(newFiles, arrayNewModules, ",")
      # `newModules` "just" stores the module names
      for(v in arrayNewModules) { newModules[arrayNewModules[v]]=0 }
    } { diff[$1]+=$2 } END {
    fileCount=0
    outputLength=0
    for(fil in diff) {
      if(!(diff[fil] == 0)) {
        fileCount++
        outputLength+=length(fil)+4
        nums[diff[fil]]++
        # we add "(new file)" next to the modules whose name appears in `newModules`
        # we separate entries with a line break, so that later we can sort the modules
        # with the same number of import differences easily
        reds[diff[fil]]=sprintf("%s `%s`%s\n", reds[diff[fil]], fil, (fil in newModules)? " (new file)" : "")
      }
    }
    if ((all == 0) && (ghLimit/2 <= outputLength)) {
      printf("There are %s files with changed transitive imports taking up over %s characters: this is too many to display!\nYou can run `scripts/import_trans_difference.sh all` locally to see the whole output.", fileCount, outputLength)
    } else {
      for(x in reds) {
        sorted=""
        split(reds[x], toSort, "\n")
        asort(toSort)
        for(i in toSort) {sorted=sorted toSort[i]}
        if (nums[x] <= 2) { printf("|%s|%s|\n", sorted, x) }
        else { printf("|<details><summary>%s files</summary>%s</details>|%s|\n", nums[x], sorted, x) }
      }
    }
  }' transImports*.txt | sort -t'|' -n -k3
  ))"
