#!/usr/bin/env bash

statsURL="https://leanprover-community.github.io/mathlib_stats.html"
mlURL="https://github.com/leanprover-community/mathlib4"

## results in 'hash YYYY-MM-DD'
hashAndDate="$(git log master --since='one week ago' --date=short --pretty="%H %ad" | tail -1)"

## just the commit hash
oldCommit="${hashAndDate/% */}"
oldCommitURL="[${oldCommit:0:10}](${mlURL}/commit/${oldCommit})"

currentCommit="$(git rev-parse HEAD)"
currentCommitURL="[${currentCommit:0:10}](${mlURL}/commit/${currentCommit})"
## just the date
date=${hashAndDate/#* /}

#####################
# Git-based reports #
#####################

## 'x files changed, y insertions(+), z deletions(-)'
gdiff="$(git diff --shortstat "${oldCommit}"..."${currentCommit}")"
gcompare="${mlURL}/compare/${oldCommit}...${currentCommit}"

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

# produces a string of the form
# ```
# Theorems
# <one_decl_name_per_row>,
# ...
# Predicates
# <one_decl_name_per_row>,
# ...
# ```
getCountDecls () {
  sed 's=^--\(count_decls\)=\1=' scripts/count_decls.lean | lake env lean --stdin |
    sed -z 's=, *=,\n=g; s=[ [#]==g; s=]=,=g; s=\n\n*=\n=g'
}

# extracts
# Theorems xx
# Predicates yy
# ...
tallyCountDecls () {
  awk 'BEGIN{ count=0 }
    /[^,]$/ { count++; type[count]=$0; acc[count]=0; }
    /,$/ { acc[count]++ } END{
    for(t=1; t<=count; t++) { printf("%s %s\n", type[t], acc[t]) }
  }' "${1}"
}

# `getKind type file` extracts all declaration names of type `type` from `file`
getKind () {
  awk -v typ="${1}$" 'BEGIN{ found=0 }
      /[^,]$/ { found=0 }
      (found == 1) { print $0 }
      ($0 ~ typ) { found=1 }' "${2}" | sort
}

# the output of `count_decls`
newDeclsTots="$(getCountDecls)"

# the tally of the output of `count_decls`
newDecls="$(echo "${newDeclsTots}" | tallyCountDecls -)"
# Definitions 73590...
git checkout -q "${oldCommit}"
# 'detached HEAD' state

lake exe cache get > /dev/null
# stuff gets downloaded

# just in case some part of the cache is corrupted
lake build --quiet

# update the `count_decls` and `mathlib_stats` scripts to the latest version
git checkout -q origin/adomani/periodic_reports_dev_custom_action scripts/count_decls.lean scripts/mathlib_stats.sh

# the output of `count_decls`
oldDeclsTots="$(getCountDecls)"

# the tally of the output of `count_decls`
oldDecls="$(echo "${oldDeclsTots}" | tallyCountDecls -)"
# Definitions 73152...

# produce the `+X -Y` report for the declarations in each category
plusMinus="$(for typ in $(echo "$newDeclsTots" | grep "[^,]$" | tr '\n' ' ');
do
  comm -123 --total <(
    echo "${newDeclsTots}" | getKind "${typ}$" -)  <(
    echo "${oldDeclsTots}" | getKind "${typ}$" -)
done)"

# produces the table summary of the declarations split by type
declSummary="$(paste -d' ' <(echo "${newDecls}") <(echo "${oldDecls}") <(echo "${plusMinus}") |
  LC_ALL=en_US.UTF-8 awk 'BEGIN{ print "|Type|Total|%|\n|:-:|:-:|:-:|" }{
    printf("| %s | %'"'"'d (+%'"'"'d -%'"'"'d) | %4.2f%% |\n", $1, $2, $5, $6, ($2-$4)*100/$2)
  }'
)"

## final report
printf -- '---\n\n## Weekly stats ([%s...%(%Y-%m-%d)T](%s))\n\n' "${date}" -1 "${gcompare}"

printf -- ' Reference commits: old %s, new %s.\n\n' "${oldCommitURL}" "${currentCommitURL}"

printf -- '%s, %s total(insertions-deletions)\n\n' "${gdiff}" "${net}"

printf -- 'Declarations:\n%s\n\nTake also a look at the [`Mathlib` stats page](%s).\n' "${declSummary}" "${statsURL}"
