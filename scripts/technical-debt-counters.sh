#!/usr/bin/env bash

# This script quantifies some of the technical debt in mathlib4.

echo "Number of porting notes:"
git grep -i "Porting note" | wc -l

echo

echo "Number of backwards compatibility flags:"
git grep "set_option.*backward" | wc -l

echo

echo "Number of adaptation notes:"
git grep "adaptation_note" | wc -l

echo

echo "Number of disabled simpNF lints:"
git grep "nolint simpNF" | wc -l

echo

echo "Number of disabled deprecation lints:"
git grep "set_option linter.deprecated false" | wc -l

echo

echo "Number of erw:"
git grep "erw \[" | wc -l

echo

echo "Number of \`Init\` files:"
git ls-files | grep "Init" | wc -l

echo

echo "Number of LoC in \`Init\` files:"
git ls-files | grep "Init" | xargs wc -l | grep total
