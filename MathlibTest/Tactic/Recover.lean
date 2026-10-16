import Mathlib.Tactic.Recover

set_option linter.unusedTactic false

/-- problematic tactic for testing recovery -/
elab "this" "is" "a" "problem" : tactic =>
  Lean.Elab.Tactic.setGoals []

/- The main test -/
example : 1 = 1 := by
  recover this is a problem
  rfl

/- Tests that recover does no harm -/
example : 3 < 4 := by
    recover decide

example : 1 = 1 := by
    recover skip; rfl

example : 2 = 2 := by
    recover skip
    rfl
