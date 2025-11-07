import Mathlib.Tactic.Common
import Mathlib.Tactic.TacticAnalysis.Declarations

set_option linter.tacticAnalysis.tryAtEachStepAesop true

/-- info: `rfl` can be replaced with `aesop` -/
#guard_msgs in
theorem foo : 2 + 2 = 4 := by
  rfl

-- Set the fraction sufficiently high that nothing will ever run.
set_option linter.tacticAnalysis.tryAtEachStep.fraction 1_000_000_000_000

#guard_msgs in
theorem bar : 2 + 2 = 4 := by
  rfl
