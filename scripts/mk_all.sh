#! /usr/bin/env bash
cd "$(git rev-parse --show-toplevel)" || exit 1
for gp in Mathlib MathlibExtras Mathlib/Tactic Counterexamples Archive
do
  git ls-files "$gp/*.lean" | LC_ALL=C sort | sed 's/\.lean//;s,/,.,g;s/^/import /' > "$gp.lean"
done
