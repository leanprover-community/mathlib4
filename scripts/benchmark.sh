#!/usr/bin/env bash
# This script should be run from a copy of `mathlib4`, with a parallel copy of `mathlib` available.
set -euo pipefail

lake exe cache get > /dev/null
lake build > /dev/null

cd ../mathlib
leanproject get-cache 2> /dev/null
leanproject build > /dev/null 2>&1

cd ../mathlib4

targets=$(cat Mathlib.lean | grep -v Mathlib.Tactic | grep -v Mathlib.Lean | grep -v Mathlib.Util \
  | grep -v Mathlib.Mathport | grep -v Mathlib.Init | grep -v Mathlib.Testing \
  | sed -e 's/import Mathlib\.//' | sed -e 's|\.|/|g')
mathlib_targets=()

for t in $targets; do
  s=$(grep "! This file was ported from Lean 3 source module" < Mathlib/$t.lean | awk '{ print $NF }' | sed -e 's|\.|/|g') || continue
  mathlib_targets+=(src/$s.lean)
  rm -f build/ir/Mathlib/$t.c
  rm -f build/ir/Mathlib/$t.c.trace
  rm -f build/lib/Mathlib/$t.olean
  rm -f build/lib/Mathlib/$t.ilean
  rm -f build/lib/Mathlib/$t.trace
  rm -f ../mathlib/src/$s.olean
done

echo "mathlib4 theory files:"
/usr/bin/time lake build > /dev/null

cd ../mathlib
echo "corresponding files in mathlib3:"
/usr/bin/time lean --make ${mathlib_targets[@]} > /dev/null

#cd ../mathlib4
#for t in $targets; do
#  s=$(grep "! This file was ported from Lean 3 source module" < Mathlib/$t.lean | awk '{ print $NF }' | sed -e 's|\.|/|g')
#  echo $t
#  lake env /usr/bin/time lean Mathlib/$t.lean > /dev/null
#  cd ../mathlib
#  /usr/bin/time lean -j1 src/$s.lean
#  cd ../mathlib4
#done
