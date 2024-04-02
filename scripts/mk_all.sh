#! /usr/bin/env bash
cd "$(git rev-parse --show-toplevel)" || exit 1
for gp in Mathlib MathlibExtras Mathlib/Tactic Counterexamples Archive
do
  ## show all the files and remove the ones that are locally `-d`eleted
  comm -23 <(git ls-files "$gp/*.lean" | sort) <(git ls-files -d "$gp/*.lean" | sort) |
    LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > "$gp.lean"
done
