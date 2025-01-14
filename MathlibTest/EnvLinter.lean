import Mathlib.Tactic.Linter.EnvLinter

def X := 0

/--
warning: using 'exit' to interrupt Lean
---
warning: /home/damiano/Matematica/Lean4/mathlib4/MathlibTest/EnvLinter.lean:19:0: warning: using 'exit' to interrupt Lean
 note: this linter can be disabled with `set_option linter.envLinter false`
---
warning: /home/damiano/Matematica/Lean4/mathlib4/MathlibTest/EnvLinter.lean:19:0: error: -- Found 1 error in 1 declarations (plus 2 automatically generated ones) in the current file with 13 linters

/- The `docBlame` linter reports:
DEFINITIONS ARE MISSING DOCUMENTATION STRINGS: -/
#check X /- definition missing documentation string -/
 note: this linter can be disabled with `set_option linter.envLinter false`
-/
#guard_msgs in
#exit

set_option linter.envLinter false
