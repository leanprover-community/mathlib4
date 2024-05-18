#!/usr/bin/env bash

statsURL="https://leanprover-community.github.io/mathlib_stats.html"

## results in 'hash YYYY-MM-DD'
hashAndDate="$(git log master --since='one week ago' --date=short --pretty="%H %ad" | tail -1)"

## just the commit hash
oldCommit="${hashAndDate/% */}"
oldCommitURL="[${oldCommit:0:10}](https://github.com/leanprover-community/mathlib4/commit/${oldCommit})"

currentCommit="$(git rev-parse HEAD)"
currentCommitURL="[${currentCommit:0:10}](https://github.com/leanprover-community/mathlib4/commit/${currentCommit})"
## just the date
date=${hashAndDate/#* /}

#####################
# Git-based reports #
#####################

## 'x files changed, y insertions(+), z deletions(-)'
gdiff="$(git diff --shortstat "${oldCommit}"...${currentCommit})"

## percentage breakdown of changes
percent="$(printf '|%%|Folder|\n|-:|:-|\n'; git diff --dirstat "${oldCommit}"...HEAD |
  sed 's=^ *=|=; s=  *=|`=g; s=$=`|='
#awk 'BEGIN{FS=" "; OFS="|"} {for(i=1; i<=NF; i++){printf $i}}'
)"

printf -v today '%(%Y-%m-%d)T\n' -1

## insertions-deletions
net=$(awk -v gd="${gdiff}" 'BEGIN{
  tot=0
  n=split(gd, gda, " ")
  for(i=2; i<=n; i++) {
    if(gda[i]+0 == gda[i]){ tot=gda[i]-tot }
  }
  print -tot }')

newDecls="$(sed 's=^--\(count_decls\)=\1 "new"=' scripts/count_decls.lean | lake env lean --stdin)"
# { defs := 73590, thms := 230958, inductives := 2451, other := 6148 }
# total: 313147
git checkout "${oldCommit}"
# 'detached HEAD' state

lake exe cache get
# stuff gets downloaded

# update the count_decls script to the latest version
git checkout -q origin/adomani/periodic_reports_dev_custom_action scripts/count_decls.lean scripts/mathlib_stats.sh

oldDecls="$(sed 's=^--\(count_decls\)=\1 "old"=' scripts/count_decls.lean | lake env lean --stdin)"
# { defs := 73152, thms := 230061, inductives := 2430, other := 6080 }
# total: 311723

declSummary="$(paste -d' ' <(echo "${newDecls}") <(echo "${oldDecls}") |
  awk 'BEGIN{ print "|Type|New|Old|Change|\n|:-:|:-:|:-:|:-:|" }{
    printf("| %s | %s | %s | %s |\n", $1, $2, $4, $2-$4)
  }'
)"

## final report
printf -- '---\n\n## Weekly stats (%s %(%Y-%m-%d)T)\n\n%s, %s total(insertions-deletions)\n\n---\n\n%s\n\n commits: old %s, current %s.\n\nDeclarations:\n%s\n\nTake also a look at the [`Mathlib` stats page](%s).\n' "${date}" -1 "${gdiff}" "${net}" "${percent}" "${oldCommitURL}" "${currentCommitURL}" "${declSummary}" "${statsURL}"

git checkout -q "${currentCommit}"
