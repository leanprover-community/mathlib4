import Mathlib.Mathport.Rename
import Mathlib.Tactic.HashCommandLinter
import Mathlib.Tactic.RunCmd
import Std.Tactic.GuardMsgs

section inactive_hash_linter
set_option linter.hashCommand false

theorem fo₁ : True := .intro
#align true fo₁

/-- info: 0 -/
#guard_msgs in
#eval 0

/-- info: constructor PUnit.unit.{u} : PUnit -/
#guard_msgs in
#print PUnit.unit

/-- info: 0 : Nat -/
#guard_msgs in
#check 0

end inactive_hash_linter

section active_hash_linter

theorem fo₂ : True := .intro
#align false fo₂

set_option linter.hashCommand true in
/--
info: 0
---
warning: `#`-commands, such as '#eval', are not allowed in 'Mathlib'
[linter.hashCommand]
-/
#guard_msgs in
#eval 0

set_option linter.hashCommand true in
/--
info: constructor PUnit.unit.{u} : PUnit
---
warning: `#`-commands, such as '#print', are not allowed in 'Mathlib'
[linter.hashCommand]
-/
#guard_msgs in
#print PUnit.unit

set_option linter.hashCommand true in
/--
info: 0 : Nat
---
warning: `#`-commands, such as '#check', are not allowed in 'Mathlib'
[linter.hashCommand]
-/
#guard_msgs in
#check 0

set_option linter.hashCommand true in
/--
info: constructor PUnit.unit.{u} : PUnit
---
warning: `#`-commands, such as '#print', are not allowed in 'Mathlib'
[linter.hashCommand]
-/
#guard_msgs in
#print PUnit.unit

-- `run_cmd` is allowed
run_cmd if false then Lean.logInfo "0"

end active_hash_linter
