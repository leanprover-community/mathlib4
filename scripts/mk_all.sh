#! /usr/bin/env bash

# Generate a file importing all the files of a Lean folder.
# By default, it generates the files for the libraries
# `Mathlib.lean`, `Mathlib/Tactic.lean`, `Archive.lean` and `Counterexamples.lean`.

##  Standard use:
##  ./scripts/mk_all.sh
##
##  updates `Mathlib` `Mathlib/Tactic` `Counterexamples` `Archive`
##
##  Advanced use:
##  ./scripts/mk_all.sh <space_separated_list_of_dirs>
##
##  for each dir in <space_separated_list_of_dirs>, create a file with all the imports of the dir
##
##  The two commands
##  ./scripts/mk_all.sh
##  ./scripts/mk_all.sh Mathlib Mathlib/Tactic Counterexamples Archive
##
##  are equivalent.

cd "$(git rev-parse --show-toplevel)" || exit 1

# assign `targets` to be the input if provided, default to "the usual Mathlib suspects" otherwise
if [ -n "${*}" ]
then
  targets=${*}
else
  targets="Mathlib Mathlib/Tactic Counterexamples Archive"
fi

## Note: *no* quotes around `${targets}`, since we want the spaces to matter
for gp in ${targets}
do
  git ls-files "$gp/*.lean" | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > "$gp.lean"
done
