import Lean.Elab.GuardMsgs
import Mathlib.Mathport.Rename
import Mathlib.Tactic.HashCommandLinter

section ignored_commands
theorem fo₁ : True := .intro
-- `#align` is allowed by the linter
#align true fo₁

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
warning: `#`-commands, such as '#guard', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs in
#guard true

/--
warning: `#`-commands, such as '#check_tactic', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs in
#check_tactic True ~> True by skip

-- Testing that the linter enters `in` recursively.

/--
warning: `#`-commands, such as '#guard', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs in
variable (n : Nat) in
#guard true

/--
warning: `#`-commands, such as '#guard', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs in
open Nat in
variable (n : Nat) in
variable (n : Nat) in
#guard true

/--
warning: `#`-commands, such as '#guard', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs in
open Nat in
variable (n : Nat) in
#guard true

end linted_commands
