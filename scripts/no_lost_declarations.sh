#!/usr/bin/env bash

## we narrow the diff to lines beginning with `theorem`, `lemma` and a few other commands
begs="(theorem|lemma|inductive|structure|def|class|instance)"

## the reference commit:
## * it *should* be the version of master from the last merge
## * it probably is the commit from where the PR branched from master
if [ -n "${1}" ]; then
  commit="${1}"
else
  commit="$( git merge-base origin/master -- "origin/$( git rev-parse --abbrev-ref HEAD )" )"
fi;

## extract lines that begin with '[+-]' followed by the input `theorem` or `lemma`
## in the `git diff`
git diff --unified=0 "${commit}" |
  awk -v regex="^[+-]${begs}" 'BEGIN{ paired=0; added=0; removed=0 }
    ($0 ~ regex){
      pm=substr($0, 1, 1)
      rest=substr($0, 2)
      acc[rest]=acc[rest] pm
    }
  END {
    fin=""
    for(res in acc) {
      pm=acc[res]
      if(pm != "-+") {
        if(pm == "+") { added++ } else removed++
        fin=fin sprintf("* `%s` `%s`\n", pm, res)
      } else paired++
    }
    print fin| "sort -k3"; close("sort -k3")
    printf("---\n* %s  added declarations\n* %s  removed declarations\n* %s  paired declarations", added, removed, paired)
  }'
printf $'\n---\n\nReference commit: `%s`\n\n---\n\nYou can run this locally using
```bash
./scripts/no_lost_declarations.sh <optional_commit>
```
' "${commit}"

 : <<ReferenceTest
theorem hello
inductives counted even if it is inductives, rather than inductive
ReferenceTest
