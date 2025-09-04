#! /usr/bin/env bash

# Run `lake exe pole $1` (defaulting to Mathlib if no argument is provided)
# and then use `lake exe unused` to investigate unused transitive imports along the longest pole.

# Create a file `unused.md` in the current directory, showing the unused transitive imports,
# and prints a `lake exe graph` commands showing the largest "rectangles" of unused imports
# (i.e. places where a large set of modules do not make use of a different large set of modules,
# even though they are transitively imported.)

# Default to Mathlib if no argument is provided
target=${1:-Mathlib}

lake exe pole --to $target | tail -n +3 | cut -f2 -d '|' | awk '{$1=$1; print}' | grep -v "Lean\." | grep -v "Init\." | grep -v "Tactic\." | grep -v "^Mathlib$" | grep -v "^Mathlib.Init$" | xargs lake exe unused
