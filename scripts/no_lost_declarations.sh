#!/usr/bin/env bash

## we narrow the diff to lines beginning with `theorem`, `lemma` and a few other commands
begs="(theorem|lemma|inductive|structure|def|class|instance)"

## if an input commit is given, compute the diff with that, otherwise, use the git-magic `...`
if [ -n "${1}" ]; then
  git diff --unified=0 "${1}"
else
  git diff origin/master...HEAD
fi |
  ## extract lines that begin with '[+-]' followed by the input `theorem` or `lemma`
  ## in the `git diff`
  awk -v regex="^[+-]${begs}" 'BEGIN{ paired=0; added=0; removed=0 }
    /^--- a\//    { minusFile=$2 }
    /^\+\+\+ b\// { plusFile=$2 }
    ($0 ~ regex){
      pm=substr($0, 1, 1)
      rest=substr($0, 2)
      fil[rest]= (pm == "+") ? plusFile : minusFile
      acc[rest]=acc[rest] pm
    }
  END {
    printf "|File|+-|Declaration|\n|-|-|-|"
    fin=""
    for(res in acc) {
      pm=acc[res]
      if(pm == "-+" || pm == "+-") { paired++ } else {
        if(pm == "+") { added++ } else removed++
        fin=fin sprintf("| %s | `%s` | `%s` |\n", fil[res], pm, res)
      }
    }
    print fin| "sort -k6 -k8"; close("sort -k6 -k8")
    printf("---\n* %s  added declarations\n* %s  removed declarations\n* %s  paired declarations", added, removed, paired)
  }'
printf $'\n---\n\nYou can run this locally using
```bash
./scripts/no_lost_declarations.sh <optional_commit>
```
'

 : <<ReferenceTest
theorem hello
inductives counted even if it is inductives, rather than inductive
ReferenceTest
