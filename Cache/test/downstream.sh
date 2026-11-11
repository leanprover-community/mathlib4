#!/usr/bin/env bash
# End-to-end test of `cache get` with a module of a downstream project.
#
# Run it from the root of a Mathlib checkout in which `lake build cache` has
# run, with no uncommitted changes to tracked files. The test copies
# `DownstreamTest/` and makes it require Mathlib by git, at this checkout's
# HEAD. Lake clones Mathlib into `.lake/packages/mathlib`, the same layout as in
# a real downstream project. `DownstreamTest.Partial` imports Mathlib only
# through the downstream module `DownstreamTest.Helper`, which imports
# `Mathlib.Data.Nat.Basic`.
#
# The test runs `lake exe cache get DownstreamTest.Partial` in the copy, with
# an empty cache directory, and checks that:
# * `cache get` asks for no file that the cache does not have, so it asks for
#   no file of a downstream module;
# * `cache get` downloads as many files as `cache get- Mathlib.Data.Nat.Basic`
#   does in this checkout;
# * `lake build DownstreamTest.Partial` then builds only the two downstream
#   modules, so `cache get` got every Mathlib cache file that they need;
# * a second `cache get DownstreamTest.Partial` downloads and unpacks nothing.
#
# The test reads the public cache, so it needs network access. If the cache
# does not have all the files of `Mathlib.Data.Nat.Basic` (for example, before
# CI builds a toolchain bump), the test stops with a notice and exits 0.

set -euo pipefail

if ! git diff --quiet HEAD --; then
  echo "::error::The test uses Mathlib at HEAD, but this checkout has uncommitted \
changes. Commit or stash them first."
  exit 1
fi

# Without this, Mathlib's `post_update` hook gets the whole cache when Lake
# resolves the dependencies of the downstream project.
export MATHLIB_NO_CACHE_ON_UPDATE=1

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Lake clones Mathlib from a one-commit copy of HEAD. Lake cannot clone from a
# shallow repository, and CI checkouts are shallow.
src=$work/mathlib
mkdir "$src"
git archive HEAD | tar -x -C "$src"
git -C "$src" init -q
git -C "$src" add -A
git -C "$src" -c user.name=cache-test -c user.email=cache-test@example.invalid \
  -c commit.gpgsign=false commit -q -m "Mathlib at $(git rev-parse HEAD)"
rev=$(git -C "$src" rev-parse HEAD)
# Lake reads the URL in the downstream `lakefile.toml`, so it must be a native
# path: `pwd -W` gives one in Git Bash on Windows.
url=$(cd "$src" && (pwd -W 2>/dev/null || pwd))

downstream=$work/DownstreamTest
cp -R "$src/DownstreamTest" "$downstream"
cp "$src/lean-toolchain" "$downstream/"
awk -v url="$url" -v rev="$rev" '
  /^path = / { print "git = \"" url "\""; print "rev = \"" rev "\""; next }
  { print }' "$src/DownstreamTest/lakefile.toml" > "$downstream/lakefile.toml"

missing="file(s) were not found in"
# The number of files in the first download attempt that the log `$1` reports.
download_count() {
  grep -m 1 -o 'Attempting to download [0-9]*' "$1" | grep -o '[0-9]*$' || true
}

MATHLIB_CACHE_DIR=$work/reference-cache lake exe cache get- Mathlib.Data.Nat.Basic 2>&1 \
  | tee "$work/reference.log"
if grep -q "$missing" "$work/reference.log"; then
  echo "::notice::The cache does not have all files of Mathlib.Data.Nat.Basic. Skipped the test."
  exit 0
fi
expected=$(download_count "$work/reference.log")

cd "$downstream"
export MATHLIB_CACHE_DIR=$work/cache
lake exe cache get DownstreamTest.Partial 2>&1 | tee get.log
if grep -q "$missing" get.log; then
  echo "::error::cache get DownstreamTest.Partial asked for files that the cache does not have."
  exit 1
fi
selected=$(download_count get.log)
if [ -z "$expected" ] || [ "$selected" != "$expected" ]; then
  echo "::error::cache get DownstreamTest.Partial downloaded ${selected:-no} files, but \
cache get- Mathlib.Data.Nat.Basic downloads ${expected:-no} files."
  exit 1
fi

lake build DownstreamTest.Partial 2>&1 | tee build.log
built=$(grep -o 'Built [A-Za-z0-9_.]*' build.log | sed 's/^Built //' | sort || true)
if [ "$built" != "$(printf 'DownstreamTest.Helper\nDownstreamTest.Partial')" ]; then
  echo "::error::lake build DownstreamTest.Partial did not build exactly the two downstream \
modules. It built:"
  echo "$built"
  exit 1
fi

lake exe cache get DownstreamTest.Partial 2>&1 | tee get-again.log
if ! grep -q "No files to download" get-again.log || grep -q "Decompressing" get-again.log; then
  echo "::error::A second cache get DownstreamTest.Partial downloaded or unpacked files."
  exit 1
fi

echo "cache get DownstreamTest.Partial got the $selected Mathlib cache files that the \
downstream modules need."
