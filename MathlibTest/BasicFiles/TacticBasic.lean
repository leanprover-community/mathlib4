module

import Mathlib.Tactic.Basic

/-! Checks that some utilities are available already when importing `Mathlib.Tactic.Basic`. -/

lemma test_lemma : True := trivial

theorem test_type_star (α : Type*) : α = α := rfl

-- Guard against the shake tool modifying our imports
/-- info: [public import Init, import Mathlib.Tactic.Basic] -/
#guard_msgs in
run_elab Lean.logInfo m!"{(← Lean.MonadEnv.getEnv).imports}"
