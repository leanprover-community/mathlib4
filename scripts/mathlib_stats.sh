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

## final report
printf -- '---\n\n## Weekly stats (%s %(%Y-%m-%d)T)\n\n%s, %s total(insertions-deletions)\n\n---\n\n%s\n\n commits: old %s, current %s.\n\nTake also a look at the [`Mathlib` stats page](%s).\n' "${date}" -1 "${gdiff}" "${net}" "${percent}" "${oldCommitURL}" "${currentCommitURL}" "${statsURL}"
