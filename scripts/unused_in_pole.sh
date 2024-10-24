# Default to Mathlib if no argument is provided
target=${1:-Mathlib}

lake exe pole --loc --to $target | tail -n +3 | cut -f2 -d '|' | awk '{$1=$1; print}' | grep -v "Lean\." | grep -v "Init\." | grep -v "Tactic\." | grep -v "^Mathlib$" | grep -v "^Mathlib.Init$" | xargs lake exe unused
