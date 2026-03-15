#! /usr/bin/env bash

: <<'BASH_MODULE_DOC'

This script runs an **experimental prototype** of certain Skimmer functionality.

While Skimmer is planned to be extensible, currently this script effectively only runs `lake build <tgt>:applyCurrentTryThis` on the specified targets, which may be configured in this script.

This script works by using a "side package" relative to the location of this script that depends on both the local package and skimmer.

`runSkimmer.sh --init` will create this side package, as long as it is local to the target package (e.g. at `packageToRefactor/scripts/runSkimmer.sh`) and all of the variables have been configured to match the refactor targets.

BASH_MODULE_DOC

# The directory in which the side-skimmer package will be created.
# I.e., the package is expected to live in `side_pkg_dir/SideSkimmer/`.
# `"$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"` yields the absolute directory containing this script, no matter the invocation location.
side_pkg_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
pkg="${side_pkg_dir}/SideSkimmer"

# The package containing the targets we want to run `lake build <tgt>:applyCurrentTryThis` on.
# Expected to be local relative to the location of this script.
target_pkg="mathlib"
# The lakefile syntax for the relative path to the package from `side_pkg_dir` / SideSkimmer.
# E.g. if we have pkg / scripts / SideSkimmer, use `'".." / ".."'`
relative_path='".." / ".."'

# The targets in that package we want to apply `lake build <tgt>:applyCurrentTryThis` to.
# May be the package, libraries in the package, or modules in the package.
# May be a bash array `("tgt1" "tgt2" ...)`
tgts=("Mathlib")

echo "Note: the functionality provided by this script is experimental and subject to change. This script will become unnecessary in the future."

if [[ "$1" == "--init" ]]; then

  mkdir -p "${pkg}"
  cat <<EOF > "${pkg}/lakefile.lean"
import Lake

open Lake DSL

package "side-skimmer"

require "skimmer" from git "https://github.com/thorimur/skimmer" @ "v0.0.1+try-this"
require ${target_pkg} from ${relative_path}
EOF
  echo "/.lake" > "${pkg}/.gitignore"
  # Creates toolchain, manifest, etc.
  (cd "${pkg}" && lake update)
else
  if [[ -f "${pkg}/lakefile.lean" && \
      -f "${pkg}/.gitignore" && \
      -f "${pkg}/lean-toolchain" && \
      -f "${pkg}/lake-manifest.json" ]]; then
    (cd "${pkg}" && lake update)
    for tgt in "${tgts[@]}"; do
      cmd=(lake build "${tgt}:applyCurrentTryThis")
      echo "Running \`${cmd[@]}\`."
      (cd "${pkg}" && "${cmd[@]}")
    done
  else
    echo "Error: \`SideSkimmer\` package is not set up."
    echo "- Ensure that the script itself is local to the targeted package and that the variables in it point at the targeted package/libraries/modules."
    echo "- Run \`runSkimmer.sh --init\` to set up \`SideSkimmer\` under \`side_pkg_dir=${side_pkg_dir}\`."
    exit 1
  fi
fi
