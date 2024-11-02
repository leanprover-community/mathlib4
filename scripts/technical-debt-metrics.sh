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
currCommit="${1:-"$(git rev-parse HEAD)"}"
refCommit="${2:-"$(git log --pretty=%H --since="$(date -I -d 'last week')" | tail -n -1)"}"

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
titlesPathsAndRegexes=(
  "porting notes"                  "*"      "Porting note"
  "backwards compatibility flags"  "*"      "set_option.*backward"
  "skipAssignedInstances flags"    "*"      "set_option tactic.skipAssignedInstances"
  "adaptation notes"               "*"      "adaptation_note"
  "disabled simpNF lints"          "*"      "nolint simpNF"
  "disabled deprecation lints"     "*"      "set_option linter.deprecated false"
  "erw"                            "*"      "erw \["
  "maxHeartBeats modifications"    ":^test" "^ *set_option .*maxHeartbeats"
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
    printf '%s|%s\n' "$(git grep "${fl}" "${regex}" "${pathspec}" | wc -l)" "${title}"
  fi
done

printf '%s|%s\n' "$(grep -c 'docBlame' scripts/nolints.json)" "documentation nolint entries"
# We count the number of large files, making sure to avoid counting the test file `test/Lint.lean`.
printf '%s|%s\n' "$(git grep '^set_option linter.style.longFile [0-9]*' Mathlib | wc -l)" "large files"
printf '%s|%s\n' "$(git grep "^open .*Classical" | grep -v " in$" -c)" "bare open (scoped) Classical"

printf '%s|%s\n' "$(wc -l < scripts/no_lints_prime_decls.txt)" "exceptions for the docPrime linter"

deprecatedFiles="$(git ls-files '**/Deprecated/*.lean' | xargs wc -l | sed 's=^ *==')"

printf '%s|%s\n' "$(printf '%s' "${deprecatedFiles}" | wc -l)" "\`Deprecated\` files"
printf '%s|%s\n\n' "$(printf '%s\n' "${deprecatedFiles}" | grep total | sed 's= total==')"  'total LoC in `Deprecated` files'
}

# collect the technical debts and the line counts of the deprecated file from the current mathlib
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

# These last two lines are needed to make the script robust against changes on disk
# that might have happened during the script execution, e.g. from switching branches
# See the top of the file for more details.
exit
}
