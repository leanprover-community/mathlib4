#!/usr/bin/env bash
# Tests the Mathlib cache in `DownstreamTest/`, a downstream project that
# requires the Mathlib checkout by path.
#
# Usage: downstream.sh SCENARIO [CACHE_OPTION...]
#
# Run it from the root of the Mathlib checkout to test. The script sets up
# `DownstreamTest/`, then runs the scenario. Each CACHE_OPTION, such as
# `--repo=OWNER/REPO`, goes to every `lake exe cache` call.
#
# Scenarios:
#
# full     `cache get` gets the cache for Mathlib and its dependencies. Then
#          `lake build --no-build Mathlib` checks that Lake accepts the oleans
#          in the downstream project.
#
# partial  `cache get DownstreamTest.Partial` gets the cache for the modules
#          that `DownstreamTest.Partial` imports. It imports Mathlib only
#          through the downstream module `DownstreamTest.Helper`, which imports
#          `Mathlib.Data.Nat.Basic`. The scenario checks that:
#          * the cache has every file that `cache get` asks for, so `cache get`
#            asks for no file of a downstream module;
#          * `cache get` downloads as many files as
#            `cache get- Mathlib.Data.Nat.Basic` in the Mathlib checkout;
#          * `lake build DownstreamTest.Partial` then builds only the two
#            downstream modules;
#          * a second `cache get` downloads and unpacks nothing.
#          Both downloads start from an empty cache directory. The build check
#          is complete only in a checkout without Mathlib oleans. If the cache
#          does not have all the files of `Mathlib.Data.Nat.Basic` (for
#          example, before CI builds a toolchain bump), the scenario stops with
#          a notice and exits 0.

set -euo pipefail

full() {
  lake exe cache "$@" get
  lake build --no-build Mathlib
}

# The number of files in the first download attempt that the log `$1` reports.
download_count() {
  grep -m 1 -o 'Attempting to download [0-9]*' "$1" | grep -o '[0-9]*$' || true
}

partial() {
  local missing expected selected built
  missing="file(s) were not found in"
  if [ -d ../.lake/build/lib/lean/Mathlib ]; then
    echo "::warning::The Mathlib checkout has Mathlib oleans, so the build check cannot show \
that cache get unpacked them."
  fi

  # The reference runs in the Mathlib checkout, so that it does not depend on how `cache`
  # works in a downstream project.
  (cd .. && MATHLIB_CACHE_DIR=$work/reference \
    lake exe cache "$@" get- Mathlib.Data.Nat.Basic) 2>&1 | tee "$work/reference.log"
  if grep -q "$missing" "$work/reference.log"; then
    echo "::notice::The cache does not have all files of Mathlib.Data.Nat.Basic. \
Skipped the partial scenario."
    return
  fi
  expected=$(download_count "$work/reference.log")

  export MATHLIB_CACHE_DIR=$work/cache
  lake exe cache "$@" get DownstreamTest.Partial 2>&1 | tee "$work/get.log"
  if grep -q "$missing" "$work/get.log"; then
    echo "::error::cache get DownstreamTest.Partial asked for files that the cache does not have."
    exit 1
  fi
  selected=$(download_count "$work/get.log")
  if [ -z "$expected" ] || [ "$selected" != "$expected" ]; then
    echo "::error::cache get DownstreamTest.Partial downloaded ${selected:-no} files, but \
cache get- Mathlib.Data.Nat.Basic downloads ${expected:-no} files."
    exit 1
  fi

  # Remove the downstream oleans of an earlier run, so that Lake builds both downstream
  # modules.
  rm -rf .lake/build
  lake build DownstreamTest.Partial 2>&1 | tee "$work/build.log"
  built=$(grep -o 'Built [A-Za-z0-9_.]*' "$work/build.log" | sed 's/^Built //' | sort || true)
  if [ "$built" != "$(printf 'DownstreamTest.Helper\nDownstreamTest.Partial')" ]; then
    echo "::error::lake build DownstreamTest.Partial did not build exactly the two downstream \
modules. It built:"
    echo "$built"
    exit 1
  fi

  lake exe cache "$@" get DownstreamTest.Partial 2>&1 | tee "$work/get-again.log"
  if ! grep -q "No files to download" "$work/get-again.log" \
      || grep -q "Decompressing" "$work/get-again.log"; then
    echo "::error::A second cache get DownstreamTest.Partial downloaded or unpacked files."
    exit 1
  fi
  echo "cache get DownstreamTest.Partial got the $selected cache files that the downstream \
modules need."
}

scenario=${1:-}
case $scenario in
  full | partial) shift ;;
  *) echo "Usage: $0 full|partial [CACHE_OPTION...]" >&2; exit 2 ;;
esac

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

cd DownstreamTest
cp ../lean-toolchain .
# Without this, Mathlib's `post_update` hook gets the whole cache, and the
# scenario tests nothing.
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
"$scenario" "$@"
