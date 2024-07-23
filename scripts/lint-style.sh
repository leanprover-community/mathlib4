#!/usr/bin/env bash

set -exo pipefail

# # Style linter

# ## Usage

# Run this script from the root of mathlib using:
# ./scripts/lint-style.sh

# ## Purpose

# The style linter checks for new style issues,
# and maintains a list of exceptions for legacy reasons.
# Ideally, the length of the list of exceptions tends to 0.

# Examples of issues that are checked for are:
# * existence of copyright header
# * existence of module docstrings (in the right place)
# * line length <= 100 (unless URL)

# ## Implementation details

# A Python script `scripts/lint-style.py` lints the contents of a Lean file.
# This script is called below on all Lean files in the repository.
# Exceptions are maintained in `scripts/style-exceptions.txt`.
# (Rewriting these checks in Lean is work in progress.)
#
# TODO: This is adapted from the linter for mathlib3. It should be rewritten in Lean.

################################################################################

# 1. Call the Lean file linter, implemented in Python

touch scripts/style-exceptions.txt

git ls-files 'Mathlib/*.lean' | xargs ./scripts/lint-style.py "$@"
git ls-files 'Archive/*.lean' | xargs ./scripts/lint-style.py "$@"
git ls-files 'Counterexamples/*.lean' | xargs ./scripts/lint-style.py "$@"

# Call the in-progress Lean rewrite of these Python lints.
lake exe lint-style --github
