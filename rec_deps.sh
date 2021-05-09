#!/usr/bin/env bash
# Usage: bash rec_deps.sh Mathlib/Plugin.lean
#
# Recursively lists all Mathlib lean files that the argument (reflexively or
# transitively) imports.

declare -A deps

go() {
  [ ${deps[$1]+_} ] && return
  deps[$1]=1
  for olean in `lean --deps "$1"`; do
    case $olean in
      */Mathlib/*.olean)
        stem=${olean#*/Mathlib/}
        stem=${stem%.olean}
        go Mathlib/$stem.lean
        ;;
    esac
  done
}

go $1

echo ${!deps[@]}
