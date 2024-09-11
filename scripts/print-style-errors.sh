#!/usr/bin/env bash

# Make this script robust against unintentional errors.
# See e.g. http://redsymbol.net/articles/unofficial-bash-strict-mode/ for explanation.
set -euo pipefail
IFS=$'\n\t'

# Print all errors of the python style linter. This script is temporary and should be removed
# once the Python style linters have been rewritten in Lean.
# Humans should never run this directly, but at most through `lean exe lint-style --fix`

# use C locale so that sorting is the same on macOS and Linux
# see https://unix.stackexchange.com/questions/362728/why-does-gnu-sort-sort-differently-on-my-osx-machine-and-linux-machine
find Mathlib -name '*.lean' | xargs ./scripts/lint-style.py "$@" | LC_ALL=C sort || true
find Archive -name '*.lean' | xargs ./scripts/lint-style.py "$@" | LC_ALL=C sort || true
find Counterexamples -name '*.lean' | xargs ./scripts/lint-style.py "$@" | LC_ALL=C sort || true
