import Mathlib.Tactic.Linter.CommandStart

/--
warning: 'section' starts on column 1, but all commands should start at the beginning of the line.
note: this linter can be disabled with `set_option linter.style.commandStart false`
-/
#guard_msgs in
 section

/--
warning: Current syntax:  'mple  '
Expected syntax: 'mple : Tru'

note: this linter can be disabled with `set_option linter.ppRoundtrip false`
-/
#guard_msgs in
example  : True := trivial

/--
warning: unused variable `a`
note: this linter can be disabled with `set_option linter.unusedVariables false`
---
warning: Current syntax:  'le (a: Nat'
Expected syntax: 'le (a : Na'

note: this linter can be disabled with `set_option linter.ppRoundtrip false`
-/
#guard_msgs in
example (a: Nat) : True := trivial
