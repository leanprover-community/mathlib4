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

variable (n₁ : Nat)
theorem X (n₁ : Nat) : n₁ = n₁ := rfl
def X_def (n₁ : Nat) : n₁ = n₁ := rfl

end A

namespace B

variable (n₂ : Nat)
theorem X : n₂ = n₂ := rfl

-- `n₂` is not unused!!
variable (n₂ : Int) in
theorem X1 : n₂ = n₂ := rfl

variable (n₂ : Int) in
theorem X11 : ‹Nat› = n₂ := by included_variables; sorry
#show_used
end B
#exit
namespace C

variable {R} [Add R] [Mul R] (r : R) in
def X : r + r = r + r := rfl

--variable {R S} [Add R] [Mul R] (r : R) in
--abbrev Y : r = r := by sorry

end C

set_option linter.unusedVariableCommand false
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
#reset_vars
#show_used

#check toFalse
GG
theorem X : True := .intro

#show_used

end GG_
