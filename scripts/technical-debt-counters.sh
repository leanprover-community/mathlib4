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

printf '%s\n%s\n\n' "Number of \`Init\` files:"        "$(git ls-files '*Init*' | wc -l)"
printf '%s\n%s\n\n' "Number of LoC in \`Init\` files:" "$(git ls-files '*Init*' | xargs wc -l | grep total)"
