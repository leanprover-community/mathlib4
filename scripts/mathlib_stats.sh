#!/usr/bin/env bash

statsURL=""

## results in 'hash YYYY-MM-DD'
hashAndDate="$(git log master --since='one week ago' --date=short --pretty="%h %ad" | tail -1)"

## just the commit hash
commit=${hashAndDate/% */}
## just the date
date=${hashAndDate/#* /}

## 'x files changed, y insertions(+), z deletions(-)'
gdiff="$(git diff --shortstat "${commit}"...HEAD)"

## percentage breakdown of changes
percent="$(git diff --dirstat "${commit}"...HEAD)"

## insertions-deletions
net=$(awk -v gd="${gdiff}" 'BEGIN{
  tot=0
  n=split(gd, gda, " ")
  for(i=2; i<=n; i++) {
    if(gda[i]+0 == gda[i]){ tot=gda[i]-tot }
  }
  print -tot }')

## final report
printf '%s, %s total((+)-(-))\n\n%s\n\n since %s (commit: %s).\n\nTake also a look at the [`Mathlib` stats page](%s).\n' "${gdiff}" "${net}" "${percent}" "${date}" "${commit}" "${statsURL}"
