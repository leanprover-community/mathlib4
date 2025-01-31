import Mathlib.Tactic.Linter.UnusedVariableCommand

open Lean Elab Command Mathlib.Linter.UnusedVariableCommand in
elab "mkt " cmd:command : command => do
  elabCommand cmd
  let thm ← mkThm cmd
  logInfo m!"{thm}"
  elabCommand thm
def toFalse (_S : Sort _) := False

set_option linter.unusedVariableCommand true
/--
info: theorem XX.sfx {a b : Nat} (c d : Int) [Add Int] : toFalse True := by included_variables plumb; sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
mkt
theorem XX {a b : Nat} (c d : Int) [Add Int] : True := .intro

/--
info: theorem D.sfx [Add Nat] [Mul Int] : False := by included_variables plumb; sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
mkt
structure D extends Add Nat, Mul Int where mk'::
  a : Nat
  b : Int

namespace A

/-
# a repeated variable name in theorem and def that is unused
-/

-- `good` unused!
variable (n₁ : Nat)
theorem X (n₁ : Nat) : n₁ = n₁ := rfl

-- ideally, uncommenting this declaration would still flag the above `n₁` as unused
--def X_def (n₁ : Nat) : n₁ = n₁ := rfl

end A

namespace B

variable (n₂ : Nat)

-- `good` unused!
theorem X : n₂ = n₂ := rfl

--  `good` unused!
variable (n₂ : Int) in
theorem X1 : n₂ = n₂ := rfl

variable (n₂ : Int) in
/--
info: Included variables:
* 'n₂' of type 'Int'
* '[anonymous]' of type 'Nat'
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
theorem X11 : ‹Nat› = n₂ := by included_variables; sorry

/--
info: Dictionary

✅️ n₂ ↔ n₂._@.MathlibTest.UnusedVariableCommand._hyg.290
❌️ n₁ ↔ n₁._@.MathlibTest.UnusedVariableCommand._hyg.275

✅️: used
❌️: unused
-/
#guard_msgs in
#show_used
end B
--#exit
namespace C

-- should error on `m` not being included!
variable {R} [Add R] [m : Mul R] (r : R) in
def X : r + r = r + r := by clear m; rfl

--variable {R S} [Add R] [Mul R] (r : R) in
--abbrev Y : r = r := by sorry

end C

--set_option linter.unusedVariableCommand false
/-
warning: using 'exit' to interrupt Lean
---
warning: 'n₁' is unused
note: this linter can be disabled with `set_option linter.unusedVariableCommand false`
---
warning: 'n₂' is unused
note: this linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
--#guard_msgs in set_option linter.unusedVariableCommand true in #exit

open Lean Elab Command Mathlib.Linter UnusedVariableCommand in
elab "GG " stx:command : command => do
  elabCommand stx
  let toThm ← mkThm stx
  logInfo m!"{toThm}"
  elabCommand toThm

namespace GG_
variable (n : Nat)
--#reset_vars
/--
info: Dictionary

✅️ n₂ ↔ n₂._@.MathlibTest.UnusedVariableCommand._hyg.290
❌️ n ↔ n._@.MathlibTest.UnusedVariableCommand._hyg.568
❌️ n₁ ↔ n₁._@.MathlibTest.UnusedVariableCommand._hyg.275

✅️: used
❌️: unused
-/
#guard_msgs in
#show_used

/--
info: theorem X.sfx : toFalse True := by included_variables plumb; sorry
---
warning: declaration uses 'sorry'
-/
#guard_msgs in
GG
theorem X : True := .intro

/--
info: Dictionary

✅️ n₂ ↔ n₂._@.MathlibTest.UnusedVariableCommand._hyg.290
❌️ n ↔ n._@.MathlibTest.UnusedVariableCommand._hyg.568
❌️ n₁ ↔ n₁._@.MathlibTest.UnusedVariableCommand._hyg.275

✅️: used
❌️: unused
-/
#guard_msgs in
#show_used

end GG_

set_option linter.unusedVariableCommand false
/--
warning: using 'exit' to interrupt Lean
---
warning: 'n₁' is unused some ((880, 884))
note: this linter can be disabled with `set_option linter.unusedVariableCommand false`
---
warning: 'n' is unused some ((2534, 2535))
note: this linter can be disabled with `set_option linter.unusedVariableCommand false`
-/
#guard_msgs in set_option linter.unusedVariableCommand true in #exit
--set_option showDefs true
set_option linter.unusedVariableCommand true
variable {C} [Add.{v} C] [Add  C]

--#exit
instance : Add.{v} C := ‹_›

instance : Add C := ‹_›

--theorem F : Nonempty (Add.{v} C) := .intro ‹_›
