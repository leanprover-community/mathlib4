import Mathlib.Tactic.TacticAnalysis.FunProp
import Mathlib.Topology.Continuous

set_option linter.tacticAnalysis.continuityToFunProp true

variable {X : Type*} [TopologicalSpace X]

/-- warning: 'fun_prop' can solve this, and is almost always faster -/
#guard_msgs in
example : Continuous (@id X) := by continuity

/--
info: Try this:
apply continuous_id
---
info: Try this:
apply continuous_id
---
warning: 'fun_prop' can solve this, and is almost always faster
-/
#guard_msgs in
example : Continuous (@id X) := by continuity?

-- TODO: also add a test for measurability!
