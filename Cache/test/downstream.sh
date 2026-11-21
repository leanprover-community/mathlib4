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
# partial  `cache get- Mathlib.Data.Nat.Basic` in the Mathlib checkout downloads
#          the reference files. Then `cache get DownstreamTest.Partial`, which
#          imports Mathlib through `DownstreamTest.Helper`, must find all its
#          files in the reference download, and `lake build` must build only
#          the two downstream modules. In a checkout with Mathlib oleans, the
#          build check is incomplete. If the server misses a reference file
#          (for example, before CI builds a toolchain bump), the scenario
#          stops with a notice and exits 0.

set -euo pipefail

full() {
  lake exe cache "$@" get
  lake build --no-build Mathlib
}

partial() {
  # Remove the oleans of an earlier run.
  rm -rf .lake/build .lake/packages/*/.lake/build
  export MATHLIB_CACHE_DIR=$work/cache
  (cd .. && lake exe cache "$@" get- Mathlib.Data.Nat.Basic) 2>&1 | tee "$work/reference.log"
  if grep -q "file(s) were not found in" "$work/reference.log"; then
    echo "::notice::The server misses files of Mathlib.Data.Nat.Basic. \
Skipped the partial scenario."
    return
  fi
  lake exe cache "$@" get DownstreamTest.Partial 2>&1 | tee "$work/get.log"
  if ! grep -q "No files to download" "$work/get.log"; then
    echo "::error::cache get DownstreamTest.Partial asked for files outside the files of \
cache get- Mathlib.Data.Nat.Basic."
    exit 1
  fi
  lake build DownstreamTest.Partial 2>&1 | tee "$work/build.log"
  local built
  built=$(grep -o 'Built [A-Za-z0-9_.]*' "$work/build.log" | sed 's/^Built //' | sort || true)
  if [ "$built" != "$(printf 'DownstreamTest.Helper\nDownstreamTest.Partial')" ]; then
    echo "::error::lake build DownstreamTest.Partial built other modules than the two \
downstream modules:"
    echo "$built"
    exit 1
  fi
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
