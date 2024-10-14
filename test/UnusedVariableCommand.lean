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
