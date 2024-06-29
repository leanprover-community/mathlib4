#!/usr/bin/env bash

# # Style exception file generator

# ## Usage

# Run this script from the root of mathlib using:
# ./scripts/update-style-exceptions.sh

# ## Purpose

# This script completely regenerates the scripts/style-exceptions.txt file.
# Typically this should only be run by automation.
# Human contributors shouldn't need to run this unless they are making changes to the linting script

# use C locale so that sorting is the same on macOS and Linux
# see https://unix.stackexchange.com/questions/362728/why-does-gnu-sort-sort-differently-on-my-osx-machine-and-linux-machine
find Mathlib -name '*.lean' | xargs ./scripts/lint-style.py | LC_ALL=C sort > scripts/style-exceptions.txt

# Append the warnings of the Lean linter, on the file length.
lake exe lint_style --update >> scripts/style-exceptions.txt
