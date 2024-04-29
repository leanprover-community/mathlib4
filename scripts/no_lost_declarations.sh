#!/usr/bin/env bash

## we narrow the diff to lines beginning with `theorem`, `lemma` and a few other commands
begs="\(theorem\|lemma\|inductive\|structure\|def\|class\|instance\)"

## the reference commit:
## * it *should* be the version of master from the last merge
## * it probably is the commit from where the PR branched from master
if [ -n "${1}" ]; then
  commit="${1}"
else
  commit="$( git merge-base master "$( git rev-parse --abbrev-ref HEAD )" )"
fi;

## extract lines that begin with '[+-]' followed by the input `theorem` or `lemma`
## in the `git diff`
git diff --unified=0 "${commit}" |
  grep "^[+-]${begs}" |
  sed 's=^\(.\)\(.*\)$=\2 \1=' |
  awk '{
    pm=$NF
    gsub(/..$/, "")
    acc[$0]=acc[$0] pm
  } END {
    fin=""
    for(res in acc) {
      pm=acc[res]
      if(pm != "-+") {
        mismatched++
        fin=fin sprintf("%s%s\n", pm == "+" ? pm "\\" : pm "\\", res)
      } else paired++
    }
    print fin| "sort -k2"
    printf("---\n%s  mismatched declarations\n%s  paired declarations", mismatched, paired)
  }' |
  column -s'\' -t
printf $'\nReference commit: %s\n\nYou can run this locally using
./scripts/no_lost_declarations.sh <optional_commit>\n' "${commit}"
