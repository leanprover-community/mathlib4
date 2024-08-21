#!/usr/bin/env bash

# Because the `lean-pr-testing-NNNN` branches use toolchains that are "updated in place"
# the cache mechanism is unreliable, so we don't test it if we are on such a branch.
if [[ ! $(cat lean-toolchain) =~ ^leanprover/lean4-pr-releases:pr-release-[0-9]+$ ]]; then
  git fetch origin master --depth 1
  git checkout origin/master
  rm -rf .lake/build/lib/Mathlib
  lake exe cache clean!
  lake exe cache get
  masterOleans="$(du --summarize --human-readable .lake)"
  git checkout -
  lake exe cache clean!
  rm -rf .lake/build/lib/Mathlib
  lake exe cache get
  newOleans="$(du --summarize --human-readable .lake)"
  printf '.lake size\nmaster: %s\nthis PR: %s' "${masterOleans}" "${newOleans}"
fi
