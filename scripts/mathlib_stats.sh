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

######################
# Lean-based reports #
######################

newDeclsTots="$(sed 's=^--\(count_decls\)=\1=' scripts/count_decls.lean | lake env lean --stdin |
  sed -z 's=, *=,\n=g; s=[ [#]==g; s=]=,=g; s=\n\n*=\n=g')"
newDecls="$(echo "${newDeclsTots}" | awk 'BEGIN{ count=0 }
  /[^,]$/ { count++; type[count]=$0; acc[count]=0; }
  /,$/ { acc[count]++ } END{
  for(t=1; t<=count; t++) { printf("%s %s\n", type[t], acc[t]) }
}')"
# Definitions 73590...
git checkout -q "${oldCommit}"
# 'detached HEAD' state

lake exe cache get #> /dev/null
# stuff gets downloaded

# update the `count_decls` and `mathlib_stats` scripts to the latest version
git checkout -q origin/adomani/periodic_reports_dev_custom_action scripts/count_decls.lean scripts/mathlib_stats.sh

oldDeclsTots="$(sed 's=^--\(count_decls\)=\1=' scripts/count_decls.lean | lake env lean --stdin |
  sed -z 's=, *=,\n=g; s=[ [#]==g; s=]=,=g; s=\n\n*=\n=g')"
oldDecls="$(echo "${oldDeclsTots}" | awk 'BEGIN{ count=0 }
  /[^,]$/ { count++; type[count]=$0; acc[count]=0; }
  /,$/ { acc[count]++ } END{
  for(t=1; t<=count; t++) { printf("%s %s\n", type[t], acc[t]) }
}')"
# Definitions 73152...

plusMinus="$(for typ in $(echo "$newDeclsTots" | grep "[^,]$" | tr '\n' ' ');
do
  comm -123 --total <(echo "${newDeclsTots}" |
    awk -v typ="${typ}$" 'BEGIN{ found=0 }
      /[^,]$/ { found=0 }
      (found == 1) { print $0 }
      ($0 ~ typ) { found=1 }' | sort)  <(echo "${oldDeclsTots}" |
    awk -v typ="${typ}$" 'BEGIN{ found=0 }
      /[^,]$/ { found=0 }
      (found == 1) { print $0 }
      ($0 ~ typ) { found=1 }' | sort) | awk '{ printf("%s %s\n", $1, $2)}'
done)"

#awk 'BEGIN{ count=0 }
#  ((NFR == NR) && (/[^,]$/))  { count++; newType[count]=$0 }
#  ((NFR == NR) && (!/[^,]$/)) { newAcc[$0]=count }
##
#  ((NFR != NR) && (/[^,]$/))  { for(t in type) { if(type[t]==$0) { count=t } }; oldType[count]=$0 }
#  ((NFR != NR) && (!/[^,]$/)) { oldAcc[$0]=count }
##
#  END{
#
#  }
#  ' <(echo "${newDeclsTots}") <(echo "${oldDeclsTots}")

declSummary="$(paste -d' ' <(echo "${newDecls}") <(echo "${oldDecls}") <(echo "${plusMinus}") |
  LC_ALL=en_US.UTF-8 awk 'BEGIN{ print "|Type|New|Change|%\n|:-:|:-:|:-:|:-:|" }{
    printf("| %s | %'"'"'d | +%'"'"'d -%'"'"'d | %'"'"'d | %4.2f%% |\n", $1, $2, $5, $6, $4, ($2-$4)*100/$2)
  }'
)"

## final report
printf -- '---\n\n## Weekly stats (%s...%(%Y-%m-%d)T)\n\n' "${date}" -1

printf -- ' Reference commits: old %s, new %s.\n\n' "${oldCommitURL}" "${currentCommitURL}"

printf -- '%s, %s total(insertions-deletions)\n\n' "${gdiff}" "${net}"

#printf -- '---\n\n%s\n\n' "${percent}"

printf -- 'Declarations:\n%s\n\nTake also a look at the [`Mathlib` stats page](%s).\n' "${declSummary}" "${statsURL}"
