#!/usr/bin/env bash

# This script quantifies some of the technical debt in mathlib4.

titles=( "Number of porting notes:"
         "Number of backwards compatibility flags:"
         "Number of adaptation notes:"
         "Number of disabled simpNF lints:"
         "Number of disabled deprecation lints:"
         "Number of erw:")

regexes=( "Porting note"
          "set_option.*backward"
          "adaptation_note"
          "nolint simpNF"
          "set_option linter.deprecated false"
          "erw \[")

for i in ${!titles[@]}; do
  if [ "${titles[$i]}" == "Number of porting notes:" ]
  then fl="-i"  # just for porting notes we ignore the case in the regex
  else fl="--"
  fi
  printf '%s\n%s\n\n' "${titles[$i]}" "$(git grep "${fl}" "${regexes[$i]}" | wc -l)"
done

initFiles="$(git ls-files '**/Init/*.lean' | xargs wc -l)"

printf '%s: %s\n\n' "Number of \`Init\` files" "$(printf '%s' "${initFiles}" | wc -l)"

printf '```spoiler %s: %s\n%s\n```\n' "Number of LoC in 'Init' files" "$(
    printf '%s\n' "${initFiles}" | grep total
  )" "$(
    printf '%s\n' "${initFiles}" | awk 'BEGIN{print"|LoC|File|\n|-:|-|"} {printf("|%s|%s|\n", $1, $2)}'
  )"
