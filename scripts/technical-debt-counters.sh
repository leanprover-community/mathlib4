#!/usr/bin/env bash

# This script quantifies some of the technical debt in mathlib4.

titlesAndRegexes=(
  "porting notes"                  "Porting note"
  "backwards compatibility flags"  "set_option.*backward"
  "adaptation notes"               "adaptation_note"
  "disabled simpNF lints"          "nolint simpNF"
  "disabled deprecation lints"     "set_option linter.deprecated false"
  "erw"                            "erw \["
)

printf '|Number|Type|\n|-:|:-|\n'
for i in ${!titlesAndRegexes[@]}; do
  # loop on the odd-indexed entries and name each entry and the following
  if (( (i + 1) % 2 )); then
    title="${titlesAndRegexes[$i]}"
    regex="${titlesAndRegexes[$(( i + 1 ))]}"
    if [ "${title}" == "porting notes" ]
    then fl="-i"  # just for porting notes we ignore the case in the regex
    else fl="--"
    fi
    printf '| %s | %s |\n' "$(git grep "${fl}" "${regex}" | wc -l)" "${title}"
  fi
done

printf '|%s | %s |\n' "$(grep -c 'docBlame' scripts/nolints.json)" "documentation nolint entries"
printf '|%s | %s |\n' "$(grep -c 'ERR_MOD' scripts/style-exceptions.txt)" "missing module docstrings"
printf '|%s | %s |\n' "$(grep -c 'ERR_NUM_LIN' scripts/style-exceptions.txt)" "large files"
# We print the number of files, not the number of matches --- hence, the nested grep.
printf '|%s | %s |\n' "$(git grep -c 'autoImplicit true' | grep -c -v 'test')" "non-test files with autoImplicit true"
printf '|%s | %s |\n' "$(git grep '@\[.*deprecated' | grep -c -v 'deprecated .*(since := "')" "deprecations without a date"

initFiles="$(git ls-files '**/Init/*.lean' | xargs wc -l)"

printf '|%s | %s |\n\n' "$(printf '%s' "${initFiles}" | wc -l)" "\`Init\` files"

printf '```spoiler %s %s\n%s\n```\n' "$(printf '%s\n' "${initFiles}" | grep total)"  "LoC in 'Init' files" "$(
    printf '%s\n' "${initFiles}" | awk 'BEGIN{print"|LoC|File|\n|-:|-|"} {printf("|%s|%s|\n", $1, $2)}'
  )"
