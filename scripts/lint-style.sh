#!/usr/bin/env bash

set -exo pipefail

# # Style linter

# ## Implementation details

# A Python script `scripts/lint-style.py` lints the contents of a Lean file.
# This script is called below on all Lean files in the repository.
# Exceptions are maintained in `scripts/style-exceptions.txt`.

################################################################################

# 1. Call the Lean file linter, implemented in Python

touch scripts/style-exceptions.txt

git ls-files 'Mathlib/*.lean' | xargs ./scripts/lint-style.py "$@"
git ls-files 'Archive/*.lean' | xargs ./scripts/lint-style.py "$@"
git ls-files 'Counterexamples/*.lean' | xargs ./scripts/lint-style.py "$@"

# Call the in-progress Lean rewrite of these Python lints.
lake exe lint-style --github
