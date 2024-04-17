import Mathlib.Tactic.Use
import Mathlib.Tactic.Congrm
import Mathlib.Tactic.TerminalRefineLinter

#guard_msgs in
example : Nat := by
  use 0

#guard_msgs in
example : Nat := by
  use! 0

#guard_msgs in
example : 0 = 0 := by
  congrm(_)

set_option linter.terminalRefine false in
set_option linter.terminalRefine true in
/--
warning: Please, use `exact` instead of `refine'`! [linter.terminalRefine]
---
warning: Please, use `exact` instead of `refine`! [linter.terminalRefine]
-/
#guard_msgs in
example : 0 = 0 ∧ 0 = 0 := by
  constructor
  refine' rfl
  refine rfl
