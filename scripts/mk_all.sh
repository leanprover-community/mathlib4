#! /usr/bin/env bash

##  Standard use:
##  ./scripts/mk_all.sh
##
##  updates `Mathlib` `MathlibExtras` `Mathlib/Tactic` `Counterexamples` `Archive`
##
##  Pro use:
##  ./scripts/mk_all.sh <space_separated_list_of_dirs>
##
##  for each dir in <space_separated_list_of_dirs>, create a file with all the imports of the dir
##
##  The two commands
##  ./scripts/mk_all.sh
##  ./scripts/mk_all.sh Mathlib MathlibExtras Mathlib/Tactic Counterexamples Archive
##
##  are equivalent.

cd "$(git rev-parse --show-toplevel)" || exit 1

# assigne `targets` to be the input or default to "the usual Mathlib suspects"
if [ -n "${*}" ]
then
  targets=${*}
else
  targets="Mathlib MathlibExtras Mathlib/Tactic Counterexamples Archive"
fi

## Note: *no* quotes around `${targets}`, since we want the spaces to matter
for gp in ${targets}
do
  git ls-files "$gp/*.lean" | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > "$gp.lean"
done
