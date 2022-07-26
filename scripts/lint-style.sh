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

# There are two parts.
# 1. A Python script `scripts/lint-style.py` that lints the contents of a Lean file.
#    This script is called below on all Lean files in the repository.
#    Exceptions are maintained in `scripts/style-exceptions.txt`.
# 2. The remainder of this shell script
#    contains some lints on the global repository.

################################################################################

# 1. Call the Lean file linter, implemented in Python

touch scripts/style-exceptions.txt

find src archive counterexamples -name '*.lean' | xargs ./scripts/lint-style.py

# 2. Global checks on the mathlib repository

# 2.1 Check for executable bit on Lean files

executable_files="$(find . -name '*.lean' -type f \( -perm -u=x -o -perm -g=x -o -perm -o=x \))"

if [[ -n "$executable_files" ]]
then
	echo "ERROR: The following Lean files have the executable bit set."
	echo "$executable_files"
	exit 1
fi

