#!/usr/bin/env bash
# End-to-end test of `cache get` with a module of a downstream project.
#
# Run it from the root of a Mathlib checkout in which `lake build cache` has run
# and which has no Mathlib build files (for example, a fresh clone in CI).
# The test creates a downstream Lake project that requires this checkout, and
# runs `lake exe cache get Downstream.Basic` in it. `Downstream.Basic` imports
# Mathlib only through the downstream module `Downstream.Helper`.
#
# The test checks that:
# * `cache get` asks for no file that the cache does not have, so it asks for
#   no file of a downstream module;
# * `lake build Downstream.Basic` then builds only the two downstream modules,
#   so `cache get` got every Mathlib cache file that they need;
# * `cache get` did not unpack `Mathlib.Topology.Basic`, which the downstream
#   modules do not import.
#
# The test reads the public cache, so it needs network access. It first runs
# `cache get- Mathlib.Data.Nat.Basic` in this checkout, which downloads the
# files that the downstream modules need but does not unpack them. If the cache
# does not have all of these files (for example, before CI builds a toolchain
# bump), the test stops with a notice and exits 0.

set -euo pipefail

if [ -e .lake/build/lib/lean/Mathlib ]; then
  echo "::error::This checkout has Mathlib build files, so the test cannot check what \
cache get unpacks. Run the test in a checkout without .lake/build/lib/lean/Mathlib."
  exit 1
fi

# Without this, Mathlib's `post_update` hook gets the whole cache when Lake
# resolves the dependencies of the downstream project.
export MATHLIB_NO_CACHE_ON_UPDATE=1

# Lake reads the path in the downstream `lakefile.toml`, so it must be a native
# path: `pwd -W` gives one in Git Bash on Windows.
mathlib=$(pwd -W 2>/dev/null || pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

cp lean-toolchain "$work/"
cat > "$work/lakefile.toml" <<EOF
name = "downstream"
defaultTargets = ["Downstream"]

[[require]]
name = "mathlib"
path = "$mathlib"

[[lean_lib]]
name = "Downstream"
EOF
mkdir -p "$work/Downstream"
cat > "$work/Downstream/Basic.lean" <<EOF
module

public import Downstream.Helper

public theorem two_add_two : 2 + 2 = 4 := helper
EOF
cat > "$work/Downstream/Helper.lean" <<EOF
module

public import Mathlib.Data.Nat.Basic

public theorem helper : 2 + 2 = 4 := rfl
EOF

missing="file(s) were not found in"
lake exe cache get- Mathlib.Data.Nat.Basic 2>&1 | tee "$work/reference.log"
if grep -q "$missing" "$work/reference.log"; then
  echo "::notice::The cache does not have all files of Mathlib.Data.Nat.Basic. Skipped the test."
  exit 0
fi

cd "$work"
lake exe cache get Downstream.Basic 2>&1 | tee get.log
if grep -q "$missing" get.log; then
  echo "::error::cache get Downstream.Basic asked for files that the cache does not have."
  exit 1
fi

if [ -e "$mathlib/.lake/build/lib/lean/Mathlib/Topology/Basic.olean" ]; then
  echo "::error::cache get Downstream.Basic unpacked Mathlib.Topology.Basic, \
which Downstream.Basic does not import."
  exit 1
fi

lake build Downstream.Basic 2>&1 | tee build.log
built=$(grep -o 'Built [A-Za-z0-9_.]*' build.log | sed 's/^Built //' | sort)
if [ "$built" != "$(printf 'Downstream.Basic\nDownstream.Helper')" ]; then
  echo "::error::lake build Downstream.Basic built other modules than the downstream modules:"
  echo "$built"
  exit 1
fi
echo "cache get Downstream.Basic got the Mathlib cache files that the downstream modules need."
