#!/usr/bin/env bash

# This script quantifies some of the technical debt in mathlib4.

titles=( "porting notes"
         "backwards compatibility flags"
         "adaptation notes"
         "disabled simpNF lints"
         "disabled deprecation lints"
         "erw")

regexes=( "Porting note"
          "set_option.*backward"
          "adaptation_note"
          "nolint simpNF"
          "set_option linter.deprecated false"
          "erw \[")

printf '|Number|Type|\n|-:|:-|\n'
for i in ${!titles[@]}; do
  if [ "${titles[$i]}" == "Number of porting notes:" ]
  then fl="-i"  # just for porting notes we ignore the case in the regex
  else fl="--"
  fi
  printf '| %s | %s |\n' "$(git grep "${fl}" "${regexes[$i]}" | wc -l)" "${titles[$i]}"
done

initFiles="$(git ls-files '**/Init/*.lean' | xargs wc -l)"

printf '|%s | %s |\n\n' "$(printf '%s' "${initFiles}" | wc -l)" "\`Init\` files"

printf '```spoiler %s %s\n%s\n```\n' "$(printf '%s\n' "${initFiles}" | grep total)"  "LoC in 'Init' files" "$(
    printf '%s\n' "${initFiles}" | awk 'BEGIN{print"|LoC|File|\n|-:|-|"} {printf("|%s|%s|\n", $1, $2)}'
  )"
