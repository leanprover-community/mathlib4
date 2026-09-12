module

public import Mathlib.Tactic.Continuity
public import Mathlib.Topology.Continuous

#eval linter.tacticAnalysis.continuityToFunProp

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
