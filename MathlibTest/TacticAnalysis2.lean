import Mathlib.Tactic.TacticAnalysis.FunProp
import Mathlib.Topology.Continuous

import Mathlib.MeasureTheory.MeasurableSpace.Basic
--import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
--import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
--import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
--import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas

set_option linter.tacticAnalysis.continuityToFunProp true

variable {X Y : Type*} [TopologicalSpace X]

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

-- TODO: see what imports make out of this!
example : Measurable (@id Y) := by measurability
