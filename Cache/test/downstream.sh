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
#          `Mathlib.Data.Nat.Basic`. First, `cache get- Mathlib.Data.Nat.Basic`
#          in the Mathlib checkout downloads the reference files into an empty
#          cache directory. Then the scenario checks that:
#          * `cache get` asks for no file outside the reference files, so it
#            downloads nothing;
#          * `lake build DownstreamTest.Partial` builds only the two downstream
#            modules, so `cache get` unpacked every olean that they need;
#          * a second `cache get` downloads and unpacks nothing.
#          The build check is complete only in a checkout without Mathlib
#          oleans. If the server does not have all the reference files (for
#          example, before CI builds a toolchain bump), the scenario stops with
#          a notice and exits 0.

set -euo pipefail

full() {
  lake exe cache "$@" get
  lake build --no-build Mathlib
}

partial() {
  # Remove the oleans of an earlier run, so that `cache get` unpacks the
  # dependency oleans and Lake builds both downstream modules.
  rm -rf .lake/build .lake/packages/*/.lake/build
  if [ -d ../.lake/build/lib/lean/Mathlib ]; then
    echo "::warning::The Mathlib checkout has Mathlib oleans, so the build check cannot show \
that cache get unpacked them."
  fi
  export MATHLIB_CACHE_DIR=$work/cache

  # The reference runs in the Mathlib checkout, so that it does not depend on how `cache`
  # works in a downstream project.
  (cd .. && lake exe cache "$@" get- Mathlib.Data.Nat.Basic) 2>&1 | tee "$work/reference.log"
  if grep -q "file(s) were not found in" "$work/reference.log"; then
    echo "::notice::The server does not have all files of Mathlib.Data.Nat.Basic. \
Skipped the partial scenario."
    return
  fi

  lake exe cache "$@" get DownstreamTest.Partial 2>&1 | tee "$work/get.log"
  if ! grep -q "No files to download" "$work/get.log"; then
    echo "::error::cache get DownstreamTest.Partial asked for files that \
cache get- Mathlib.Data.Nat.Basic does not download."
    exit 1
  fi

  local built
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
  echo "cache get DownstreamTest.Partial got the cache files that the downstream modules need."
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
# This skips `cache get` in Mathlib's `post_update` hook, so the `cache get` of
# the scenario is the first one.
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
"$scenario" "$@"
