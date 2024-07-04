import Lean.Elab.GuardMsgs
import Mathlib.Mathport.Rename
import Mathlib.Tactic.AdaptationNote
import Mathlib.Tactic.Linter.HashCommandLinter

section ignored_commands
theorem fo₁ : True := .intro
-- `#align` is allowed by the linter
#align true fo₁

-- `#guard_msgs in` without a doc-string triggers the linter, but with the `doc-string does not
/--
warning: `#`-commands, such as '#guard_msgs', are not allowed in 'Mathlib'
note: this linter can be disabled with `set_option linter.hashCommand false`
-/
#guard_msgs in
#guard_msgs in
#adaptation_note /-- testing that the hashCommand linter ignores this. -/

/-- info: 0 -/
#guard_msgs in
-- emits a message -- the linter allows it
#eval 0

/-- info: constructor PUnit.unit.{u} : PUnit -/
#guard_msgs in
-- emits a message -- the linter allows it
#print PUnit.unit

/-- info: 0 : Nat -/
#guard_msgs in
-- emits a message -- the linter allows it
#check 0

/--
info:
-/
#guard_msgs in
-- emits an empty message -- the linter allows it
#eval show Lean.MetaM _ from do guard true

-- not a `#`-command and not emitting a message: the linter allows it
run_cmd if false then Lean.logInfo "0"
end ignored_commands

section linted_commands
/--
warning: `#`-commands, such as '#guard', are not allowed in 'Mathlib'
note: this linter can be disabled with `set_option linter.hashCommand false`
-/
#guard_msgs in
#guard true

/--
warning: `#`-commands, such as '#check_tactic', are not allowed in 'Mathlib'
note: this linter can be disabled with `set_option linter.hashCommand false`
-/
#guard_msgs in
#check_tactic True ~> True by skip

-- Testing that the linter enters `in` recursively.

/--
warning: `#`-commands, such as '#guard', are not allowed in 'Mathlib'
note: this linter can be disabled with `set_option linter.hashCommand false`
-/
#guard_msgs in
variable (n : Nat) in
#guard true

/--
warning: `#`-commands, such as '#guard', are not allowed in 'Mathlib'
note: this linter can be disabled with `set_option linter.hashCommand false`
-/
#guard_msgs in
open Nat in
variable (n : Nat) in
variable (n : Nat) in
#guard true

/--
warning: `#`-commands, such as '#guard', are not allowed in 'Mathlib'
note: this linter can be disabled with `set_option linter.hashCommand false`
-/
#guard_msgs in
open Nat in
variable (n : Nat) in
#guard true

-- a test for `withSetOptionIn'`
set_option linter.unusedVariables false in
example {n : Nat} : Nat := 0

section warningAsError

-- if `warningAsError = true`, log an info (instead of a warning) on all `#`-commands, noisy or not
set_option warningAsError true
/--
info: 0
---
info: `#`-commands, such as '#eval', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs in
#eval 0

/--
info: `#`-commands, such as '#guard', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs in
#guard true

end warningAsError

end linted_commands
