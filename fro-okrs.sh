#!/usr/bin/env bash

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail

# We need to make the script robust against changes on disk
# that might have happened during the script execution, e.g. from switching branches.
# We do that by making sure the entire script is parsed before execution starts
# using the following pattern
# {
# # script content
# exit
# }
# (see https://stackoverflow.com/a/2358432).
# So please do not delete the following line, or the final two lines of this script.
{

IFS=$'\n\t'

# `./fro-okrs.sh` returns a tally of some technical debts in current Mathlib,
# reporting also the change with respect to the same counts in Mathlib from last week.
# This is intended for measuring progress with respect to the Lean FRO's OKRs.

# the script takes two optional arguments `<optCurrCommit> <optReferenceCommit>`
# and tallies the same technical debts on `<optCurrCommit>` using `<optReferenceCommit>`
# as a reference.
# If `$1` is supplied and is not `pr_summary`, then we use it; otherwise, we fall back to
# `$(git rev-parse HEAD)`.
# Similarly for the second argument: if `$1` (note the 1, not 2!) is `pr_summary`, then we use
# the closest version of master that we can find to the current commit. Otherwise we use the second
# input, falling back to a commit from last week if `$2` is not provided.
case "${1:-}" in
  pr_summary)
    currCommit="$(git rev-parse HEAD)"
    refCommit="$(git merge-base origin/master HEAD)"
    >&2 printf '***  pr_summary passed  ***\n'
    ;;
  *)
    currCommit="${1:-"$(git rev-parse HEAD)"}"
    if date -v -7d > /dev/null 2>&1; then
      date="$(date -v -7d)"
    else
      date="$(date --date="last week")"
    fi
    refCommit="${2:-"$(git log --pretty=%H --since="$date" | tail -n -1)"}"
    >&2 printf '***  NO pr_summary passed  ***\n'
    ;;
esac

## `computeDiff input` assumes that input consists of lines of the form `value|description`
## where `value` is a number and `description` is the statistic that `value` reports.
## `value` is non-negative, if it refers to the current commit and it is negative otherwise.
## The output is of the form `|current value|difference|description|`.
computeDiff () {
  gawk -F'|' 'BEGIN{
        con=1
        initial["porting notes"]=1798
        goal["porting notes"]=1500
        weight["porting notes"]=20

        initial["adaptation notes"]=200
        goal["adaptation notes"]=150
        weight["adaptation notes"]=0

        initial["disabled simpNF lints"]=200
        goal["disabled simpNF lints"]=0
        weight["disabled simpNF lints"]=0

        initial["erw"]=1500
        goal["erw"]=1000
        weight["erw"]=0

        initial["maxHeartBeats modifications"]=16
        goal["maxHeartBeats modifications"]=10
        weight["maxHeartBeats modifications"]=0

        initial["large files"]=12
        goal["large files"]=0
        weight["large files"]=10
      }{
      # order keeps track of maintaining the final order of the counters the same as the input one
      # rdict stores the difference of the current value minus the old value
      # curr stores the current value, making sure that the number is non-negative and does not start with `-`
      if(rdict[$2] == "") {order[con]=$2; con++}
      if((0 <= $1+0) && (!($1 ~ "-"))) {curr[$2]=$1}
      rdict[$2]+=$1+0
    } END {
    # loop over the "sorted" index in `order`
    total_progress=0
    for(ind=1; ind<=con-1; ind++) {
      # retrieve the description of the counter
      val=order[ind]
      progress=(initial[val] - curr[val]) / (initial[val] - goal[val])
      progress=(progress > 1) ? 1 : progress
      contribution=weight[val] * progress
      total_progress+=contribution+0
      # print `|name|start|current|goal|difference|contribution|`
      printf("|%s|%s|%s|%s|%s|%s|\n", val, initial[val], curr[val], goal[val], rdict[val], contribution)
    }
    printf("\nOKR progress: %s%%", total_progress)
  }' "${1}"
}

# `tdc` produces a semi-formatted output of the form
# ...
# <number>|description
# ...
# summarizing technical debts in Mathlib.
# The script uses the fact that a line represents a technical debt if and only if the text before
# the first `|` is a number.  This is then used for comparison and formatting.
tdc () {
titlesPathsAndRegexes=(
  "porting notes"                  "*"      "Porting note"
  "adaptation notes"               "*"      "adaptation_note"
  "disabled simpNF lints"          "*"      "nolint simpNF"
  "erw"                            "*"      "erw \["
  "maxHeartBeats modifications"    ":^MathlibTest" "^ *set_option .*maxHeartbeats"
)

for i in ${!titlesPathsAndRegexes[@]}; do
  # loop on every 3rd entry and name that entry and the following two
  if (( i % 3 == 0 )); then
    title="${titlesPathsAndRegexes[$i]}"
    pathspec="${titlesPathsAndRegexes[$(( i + 1 ))]}"
    regex="${titlesPathsAndRegexes[$(( i + 2 ))]}"
    if [ "${title}" == "porting notes" ]
    then fl="-i"  # just for porting notes we ignore the case in the regex
    else fl="--"
    fi
    printf '%s|%s\n' "$(git grep "${fl}" "${regex}" -- "${pathspec}" | wc -l | tr -d ' ')" "${title}"
  fi
done

# We count the number of large files, making sure to avoid counting the test file `MathlibTest/Lint.lean`.
printf '%s|%s\n' "$(git grep '^set_option linter.style.longFile [0-9]*' Mathlib | wc -l | tr -d ' ')" "large files"
}

report () {

# Collect the technical debt metrics and the line counts of all deprecated files from current mathlib.
git checkout -q "${currCommit}"
new="$(tdc)"
git switch -q -

# collect the technical debts and the line counts of the deprecated file from the reference mathlib
git checkout -q "${refCommit}"
old="$(tdc | sed 's=^[0-9]=-&=')"
git switch -q -

printf '|Name|Start|Current|Target|∆-week|OKR contribution|\n|:-|-:|-:|-:|:-:|-:|\n'
printf '%s\n%s\n' "${old}" "${new}" | computeDiff -

baseURL='https://github.com/leanprover-community/mathlib4/commit'
printf '\nCurrent commit [%s](%s)\n' "${currCommit:0:10}" "${baseURL}/${currCommit}"
printf 'Reference commit [%s](%s)\n' "${refCommit:0:10}"  "${baseURL}/${refCommit}"
}

if [ "${1:-}" == "pr_summary" ]
then
  rep="$(report | gawk -F'|' 'BEGIN{backTicks=0} /^```/{backTicks++} ((!/^```/) && (backTicks % 2 == 0) && !($3 == "0")) {print $0}')"
  if [ "$(wc -l <<<"${rep}")" -le 5 ]
  then
    printf '<details><summary>No changes to technical debt.</summary>\n'
  else
    printf '%s\n' "${rep}" |
      gawk -F '|' -v rep="${rep}" '
        BEGIN{total=0; weight=0}
        (($3+0 == $3) && (!($2+0 == 0))) {total+=1 / $2; weight+=$3 / $2}
        END{
          average=weight/total
          if(average < 0) {change= "Decrease"; average=-average; weight=-weight} else {change= "Increase"}
          printf("<details><summary>%s in tech debt: (relative, absolute) = (%4.2f, %4.2f)</summary>\n\n%s\n", change, average, weight, rep) }'
  fi
  printf '\nYou can run this locally as\n```\n./fro-okrs.sh pr_summary\n```\n%s\n</details>\n' '* The `relative` value is the weighted *sum* of the differences with weight given by the *inverse* of the current value of the statistic.
* The `absolute` value is the `relative` value divided by the total sum of the inverses of the current values (i.e. the weighted *average* of the differences).'
else
  report
fi

# These last two lines are needed to make the script robust against changes on disk
# that might have happened during the script execution, e.g. from switching branches
# See the top of the file for more details.
exit
}
