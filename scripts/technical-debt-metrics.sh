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

# `./scripts/technical-debt-metrics.sh` returns a tally of some technical debts in current Mathlib,
# reporting also the change with respect to the same counts in
# Mathlib from last week.

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
    refCommit="${2:-"$(git log --pretty=%H --since="$(date -I -d 'last week')" | tail -n -1)"}"
    >&2 printf '***  NO pr_summary passed  ***\n'
    ;;
esac

## `computeDiff input` assumes that input consists of lines of the form `value|description`
## where `value` is a number and `description` is the statistic that `value` reports.
## `value` is non-negative, if it refers to the current commit and it is negative otherwise.
## The output is of the form `|current value|difference|description|`.
computeDiff () {
  awk -F'|' 'BEGIN{con=1}{
      # order keeps track of maintaining the final order of the counters the same as the input one
      # rdict stores the difference of the current value minus the old value
      # curr stores the current value, making sure that the number is non-negative and does not start with `-`
      if(rdict[$2] == "") {order[con]=$2; con++}
      if((0 <= $1+0) && (!($1 ~ "-"))) {curr[$2]=$1}
      rdict[$2]+=$1+0
    } END {
    # loop over the "sorted" index in `order`
    for(ind=1; ind<=con-1; ind++) {
      # retrieve the description of the counter
      val=order[ind]
      # print `|current value|difference|name of counter|`
      printf("|%s|%s|%s|\n", curr[val], rdict[val], val)}
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
# We perform word-splitting "by hand" in the "middle" entries.
# See also the comment on the `read` line in the for-loop that follows the definition of this array.
titlesPathsAndRegexes=(
  "porting notes"                  "*"      "Porting note"
  "backwards compatibility flags"  "*"      "set_option.*backward"
  "skipAssignedInstances flags"    "*"      "set_option tactic.skipAssignedInstances"
  "adaptation notes"               ":^Mathlib/Tactic/AdaptationNote.lean :^Mathlib/Tactic/Linter"
                                            "^[· ]*#adaptation_note"
  "disabled simpNF lints"          "*"      "nolint simpNF"
  "erw"                            "*"      "erw \["
  "maxHeartBeats modifications"    ":^MathlibTest" "^ *set_option .*maxHeartbeats.* [0-9][0-9]*"
  "CommRing (Fin n) instances"     "*"      "^open Fin.CommRing "
  "NatCast (Fin n) instances"      "*"      "^open Fin.NatCast "
)

for i in ${!titlesPathsAndRegexes[@]}; do
  # loop on every 3rd entry and name that entry and the following two
  if (( i % 3 == 0 )); then
    title="${titlesPathsAndRegexes[$i]}"
    # Here we perform word-splitting: `pathspec` is an array whose entries are the "words" in
    # the string `"${titlesPathsAndRegexes[$(( i + 1 ))]}"`.
    read -r -a pathspec <<< "${titlesPathsAndRegexes[$(( i + 1 ))]}"
    regex="${titlesPathsAndRegexes[$(( i + 2 ))]}"
    if [ "${title}" == "porting notes" ]
    then fl="-i"  # just for porting notes we ignore the case in the regex
    else fl="--"
    fi
    printf '%s|%s\n' "$(git grep "${fl}" "${regex}" -- ":^scripts" "${pathspec[@]}" | wc -l)" "${title}"
  fi
done

# count total number of `set_option linter.deprecated false` outside of `Mathlib/Deprecated`
deprecs="$(git grep -c -- "set_option linter.deprecated false" -- ":^Mathlib/Deprecated" |
  awk -F: 'BEGIN{total=0} {total+=$2} END{print total}')"

# count the `linter.deprecated` exceptions that are themselves followed by `deprecated ...(since`
# we subtract these from `deprecs`
doubleDeprecs="$(git grep -A2 -- "set_option linter.deprecated false" -- ":^Mathlib/Deprecated" |
  grep -c "deprecated .*(since")"

printf '%s|disabled deprecation lints\n' "$(( deprecs - doubleDeprecs ))"

printf '%s|%s\n' "$(grep -c 'docBlame' scripts/nolints.json)" "documentation nolint entries"
# We count the number of large files, making sure to avoid counting the test file `MathlibTest/Lint.lean`.
printf '%s|%s\n' "$(git grep '^set_option linter.style.longFile [0-9]*' Mathlib | wc -l)" "large files"

printf '%s|%s\n' "$(wc -l < scripts/nolints_prime_decls.txt)" "exceptions for the docPrime linter"

deprecatedFiles="$(git ls-files '**/Deprecated/*.lean' | xargs wc -l | sed 's=^ *==')"

printf '%s|%s\n' "$(printf '%s' "${deprecatedFiles}" | wc -l)" "\`Deprecated\` files"
printf '%s|%s\n\n' "$(printf '%s\n' "${deprecatedFiles}" | grep total | sed 's= total==')"  'total LoC in `Deprecated` files'
}

report () {

# Collect the technical debt metrics and the line counts of all deprecated files from current mathlib.
git checkout -q "${currCommit}"
new="$(tdc)"
newDeprecatedFiles="$(git ls-files '**/Deprecated/*.lean' | xargs wc -l | sed 's=^ *==')"
git switch -q -

# collect the technical debts and the line counts of the deprecated file from the reference mathlib
git checkout -q "${refCommit}"
old="$(tdc | sed 's=^[0-9]=-&=')"
oldDeprecatedFiles="$(git ls-files '**/Deprecated/*.lean' | xargs wc -l | sed 's=^ *=-=')"
git switch -q -

printf '|Current number|Change|Type|\n|-:|:-:|:-|\n'
printf '%s\n%s\n' "${old}" "${new}" | computeDiff -
deprSummary="$(printf '%s\n%s\n' "${oldDeprecatedFiles}" "${newDeprecatedFiles}" | tr ' ' '|' | computeDiff -)"

printf $'```spoiler Changed \'Deprecated\' lines by file\n%s\n```\n' "$(
    printf '%s\n' "${deprSummary}" | awk -F'|' 'BEGIN{print("|LoC|Change|File|\n|-:|:-:|-|")}
    ($4 == "total") {total=$0}
    (!($4 == "total")) {
      printf("%s\n", $0)
    } END {printf("%s\n", total)}'
  )"

baseURL='https://github.com/leanprover-community/mathlib4/commit'
printf '\nCurrent commit [%s](%s)\n' "${currCommit:0:10}" "${baseURL}/${currCommit}"
printf 'Reference commit [%s](%s)\n' "${refCommit:0:10}"  "${baseURL}/${refCommit}"
}

if [ "${1:-}" == "pr_summary" ]
then
  rep="$(report | awk -F'|' 'BEGIN{backTicks=0} /^```/{backTicks++} ((!/^```/) && (backTicks % 2 == 0) && !($3 == "0")) {print $0}')"
  if [ "$(wc -l <<<"${rep}")" -le 5 ]
  then
    printf '<details><summary>No changes to technical debt.</summary>\n'
  else
    printf '%s\n' "${rep}" |  # outputs lines containing `|Current number|Change|Type|`, so
                              # `$2` refers to `Current number` and `$3` to `Change`.
      awk -F '|' -v rep="${rep}" '
        BEGIN{total=0; weight=0; absWeight=0}
        {absWeight+=$3+0}
        (($3+0 == $3) && (!($2+0 == 0))) {total+=1 / $2; weight+=$3 / $2}
        END{
          if (total == 0) {average=absWeight} else {average=weight/total}
          if(average < 0) {change= "Decrease"; average=-average; weight=-weight} else {change= "Increase"}
          printf("<details><summary>%s in tech debt: (relative, absolute) = (%4.2f, %4.2f)</summary>\n\n%s\n", change, average, weight, rep) }'
  fi
  printf '\nYou can run this locally as\n```\n./scripts/technical-debt-metrics.sh pr_summary\n```\n%s\n</details>\n' '* The `relative` value is the weighted *sum* of the differences with weight given by the *inverse* of the current value of the statistic.
* The `absolute` value is the `relative` value divided by the total sum of the inverses of the current values (i.e. the weighted *average* of the differences).'
else
  report
fi

# These last two lines are needed to make the script robust against changes on disk
# that might have happened during the script execution, e.g. from switching branches
# See the top of the file for more details.
exit
}
