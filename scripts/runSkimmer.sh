#! /usr/bin/env bash

: <<'BASH_MODULE_DOC'

This script runs an **experimental prototype** of certain Skimmer functionality.

While Skimmer is planned to be extensible, currently this script effectively only runs `lake build <tgt>:applyCurrentTryThis` on the specified targets, which may be configured in this script.

This script works by using a "side package" relative to the location of this script that depends on both the local package and skimmer.

`runSkimmer.sh --init` will create this side package, as long as it is local to the target package (e.g. at `packageToRefactor/scripts/runSkimmer.sh`) and all of the variables have been configured to match the refactor targets.

Report issues to Thomas Murrills, on Zulip, either by DM or on the following channel:
https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/automatically.20apply.20code.20actions

BASH_MODULE_DOC

# ---------------------------------------------
# Config variables (specific to target package)
# ---------------------------------------------

# The directory in which the side-skimmer package will be created.
# I.e., the package is expected to live in `side_pkg_dir/SideSkimmer/`.
# `"$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"` yields the absolute directory containing this script, no matter the invocation location.
side_pkg_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
pkg="${side_pkg_dir}/SideSkimmer"

# The package containing the targets we want to run `lake build <tgt>:applyCurrentTryThis` on.
# Expected to be local relative to the location of this script.
target_pkg="mathlib"
# The lakefile syntax for the relative path to the target package from `side_pkg_dir` / SideSkimmer.
# E.g. if we have target_pkg / scripts / SideSkimmer, use `'".." / ".."'`
relative_path='".." / ".."'

# The targets in the target package on which we will run `lake build <tgt>:applyCurrentTryThis`.
# May use lake target syntax; may be the whole package or libraries or modules in the package.
# May be a bash array `("tgt1" "tgt2" ...)`; will refactor each in turn.
tgts=("Mathlib")

# --------------------
# End config variables
# --------------------

echo "Note: the functionality provided by this script is experimental and subject to change. This script will become unnecessary in the future."
echo "Please report any issues (especially incomprehensible ones!) to Thomas Murrills on Zulip."

usage() {
  cat <<EOF
Usage: runSkimmer.sh [[--no-update] [--on [tgts...]] | --lake-update | --init | -h | --help]

Options:
  [no arguments]  Run \`lake update\` in \`SideSkimmer\`, then run \`lake build <tgt>:applyCurrentTryThis\` on targets configured in \`runSkimmer.sh\`. (When refactoring mathlib, does not get mathlib's cache.)
  --on [tgts...]  Run \`lake update\` in \`SideSkimmer\`, then run \`lake build <tgt>:applyCurrentTryThis\` for \`tgt\` in the supplied \`tgts\`. Each `tgt` may be lake target syntax for the current package or a library or module therein. (When refactoring mathlib, does not get mathlib's cache.)
  --no-update     Only run \`lake build <tgts>:applyCurrentTryThis\`, without first running \`lake update\` in \`SideSkimmer\`. Applies both the default targets and those supplied with \`--on\`.
  --init          Set up the \`SideSkimmer\` side package. This only needs to be done when first introducing \`runSkimmer.sh\` to a new repo.
  --lake-update   Only run \`lake update -v\` in \`SideSkimmer\`, and if refactoring mathlib, do not get mathlib's cache while doing so.
EOF
}

checkNoArg() {
  if [[ -n "$1" ]]; then
    echo "Unexpected argument \`$1\`"
    usage
    exit 1
  fi
}

# Argument handling:
if [[ "$1" == "-h" || "$1" == "--help" ]]; then
  checkNoArg "$2"
  usage
  exit 0
elif [[ "$1" == "--init" ]]; then
  checkNoArg "$2"
  shouldInit=true
elif [[ "$1" == "--lake-update" ]]; then
  checkNoArg "$2"
  lakeUpdate=true
elif [[ "$1" == "--no-update" || "$1" == "--on" ]]; then
  if [[ "$1" == "--no-update" ]]; then
    noUpdate=true
    shift
  fi
  if [[ "$1" == "--on" ]]; then
    tgts=("${@:2}")
  else
    checkNoArg "$1"
  fi
else
  checkNoArg "$1"
fi

# If we're refactoring mathlib, don't get the cache.
# If not, mathlib may be a dependency, in which case it will live in `SideSkimmer/.lake/packages`.
# TODO: duplicating the oleans is not ideal. Can we re-use the packages already available locally?
# Setting `packagesDir` does not seem to work.
if [[ "${target_pkg}" == "mathlib" ]]; then
  export MATHLIB_NO_CACHE_ON_UPDATE=1
fi

if [[ "${shouldInit}" ]]; then
  mkdir -p "${pkg}"
  cat <<EOF > "${pkg}/lakefile.lean"
import Lake

open Lake DSL

package "side-skimmer"

require "skimmer" from git "https://github.com/thorimur/skimmer" @ "v0.0.1+try-this"
require ${target_pkg} from ${relative_path}
EOF
  # Ignore things changed by `lake update`, update locally on individual runs.
  cat <<EOF > "${pkg}/.gitignore"
/.lake
/lake-manifest.json
/lean-toolchain
EOF
  # Creates toolchain, manifest, etc.
  (cd "${pkg}" && lake update)
else
  if [[ -f "${pkg}/lakefile.lean" && -f "${pkg}/.gitignore" ]]; then
    if [[ "${lakeUpdate}" ]]; then
      echo "Only running \`lake update -v\` in \`SideSkimmer\`; skipping run."
      (cd "${pkg}" && lake update -v)
      exit 0
    fi
    # Only run `lake update` if `--no-update` is not present.
    if [[ ! "${noUpdate}" ]]; then
      echo "Running \`lake update\` in \`SideSkimmer\`. Use \`runSkimmer.sh --no-update\` to skip this step."
      (cd "${pkg}" && lake update)
    elif [[ ! -f "${pkg}/lake-manifest.json" ]]; then
      echo "Expected manifest at \`${pkg}/lake-manifest.json\`."
      echo "Please exclude the \`--no-update\` flag to create one."
      exit 1
    elif [[ ! -f "${pkg}/lean-toolchain" ]]; then
      echo "Expected toolchain at \`${pkg}/lean-toolchain\`."
      echo "Please exclude the \`--no-update\` flag to create one."
      exit 1
    fi
    echo "Note: \`runSkimmer.sh\` uses available oleans from the targeted package and builds necessary ones. Consider getting the cache prior to running if possible."
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
