#!/usr/bin/env bash

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

# `./scripts/technical-debt-metrics.sh` returns a tally of some technical debts in current Mathlib,
# reporting also the change with respect to the same counts in
# Mathlib from last week.

# the script takes two optional arguments `<optCurrCommit> <optReferenceCommit>`
# and tallies the same technical debts on `<optCurrCommit>` using `<optReferenceCommit>`
# as a reference.

if [ -n "${1}" ]; then
  currCommit="${1}"
else
  currCommit="$(git rev-parse HEAD)"
fi

if [ -n "${2}" ]; then
  refCommit="${2}"
else
  refCommit="$(git log --pretty=%H --since="$(date -I -d 'last week')" | tail -n -1)"
fi

# `tdc` produces a semi-formatted output of the form
# ...
# <number>|description
# ...
# summarizing technical debts in Mathlib.
# The script uses the fact that a line represents a technical debt if and only if the text before
# the first `|` is a number.  This is then used for comparison and formatting.
tdc () {
titlesAndRegexes=(
  "porting notes"                  "Porting note"
  "backwards compatibility flags"  "set_option.*backward"
  "skipAssignedInstances flags"    "set_option tactic.skipAssignedInstances"
  "adaptation notes"               "adaptation_note"
  "disabled simpNF lints"          "nolint simpNF"
  "disabled deprecation lints"     "set_option linter.deprecated false"
  "erw"                            "erw \["
  "maxHeartBeats modifications"    "^ *set_option .*maxHeartbeats"
)

printf '|Current number|Change|Type|\n|-:|:-:|:-|\n'
for i in ${!titlesAndRegexes[@]}; do
  # loop on the odd-indexed entries and name each entry and the following
  if (( (i + 1) % 2 )); then
    title="${titlesAndRegexes[$i]}"
    regex="${titlesAndRegexes[$(( i + 1 ))]}"
    if [ "${title}" == "porting notes" ]
    then fl="-i"  # just for porting notes we ignore the case in the regex
    else fl="--"
    fi
    printf '%s|%s\n' "$(git grep "${fl}" "${regex}" | wc -l)" "${title}"
  fi
done

printf '%s|%s\n' "$(grep -c 'docBlame' scripts/nolints.json)" "documentation nolint entries"
# We count the number of large files, making sure to avoid counting the test file `test/Lint.lean`.
printf '%s|%s\n' "$(git grep '^set_option linter.style.longFile [0-9]*' Mathlib | wc -l)" "large files"
printf '%s|%s\n' "$(git grep "^open .*Classical" | grep -v " in$" -c)" "bare open (scoped) Classical"
# We print the number of files, not the number of matches --- hence, the nested grep.
printf '%s|%s\n' "$(git grep -c 'autoImplicit true' | grep -c -v 'test')" "non-test files with autoImplicit true"

deprecatedFiles="$(git ls-files '**/Deprecated/*.lean' | xargs wc -l | sed 's=^ *==')"

printf '%s|%s\n' "$(printf '%s' "${deprecatedFiles}" | wc -l)" "\`Deprecated\` files"
printf '%s|%s\n' "$(printf '%s\n' "${deprecatedFiles}" | grep total | sed 's= total==')"  'total LoC in `Deprecated` files'

initFiles="$(git ls-files '**/Init/*.lean' | xargs wc -l | sed 's=^ *==')"

printf '%s|%s\n' "$(printf '%s' "${initFiles}" | wc -l)" "\`Init\` files"
printf '%s|%s\n\n' "$(printf '%s\n' "${initFiles}" | grep total | sed 's= total==')"  'total LoC in `Init` files'

printf $'```spoiler Changed \'Init\' lines by file\n%s\n```\n' "$(
    printf '%s\n' "${initFiles}" | awk 'BEGIN{print("|LoC|Change|File|\n|-:|:-:|-|")} {printf("%s|%s\n", $1, $2)}'
  )"
}

# collect the technical debts from the current mathlib
new="$(git checkout -q "${currCommit}" && tdc; git switch -q -)"

# collect the technical debts from the reference mathlib -- switch to the
old="$(git checkout -q "${refCommit}" && tdc; git switch -q -)"

# place the outputs side-by-side, using `@` as a separator
paste -d@ <(echo "$new") <(echo "${old}") | sed 's=@=|@|=' |
  # each line should look like eithe
  # [new number]|description@[old number]|descr
  # or something that does not start with [number]|
  # we split the lines into "words", using `|` as a separator
  awk -F'|' '
    # if the first "word" is a number, then we write the 1st entry and compare it with the 4th
    ($1+0 == $1) { printf("|%s|%s|%s|\n", $1, $1-$4, $2) }
    # otherwise, the line is a "formatting" line, so we simply print it unchanged until we find `@`
    !($1+0 == $1) {
      for(i=1; i<=NF; i++) {
        if ($i == "@") { break }
        else { printf("%s|", $i) }
      }
      print "@"
    }' |
  # the sequence `@|` ending a line is an artifact of our process and we remove it
  sed 's=|@$=='

baseURL='https://github.com/leanprover-community/mathlib4/commit'
printf '\nCurrent commit [%s](%s)\n' "${currCommit:0:10}" "${baseURL}/${currCommit}"
printf 'Reference commit [%s](%s)\n' "${refCommit:0:10}"  "${baseURL}/${refCommit}"
