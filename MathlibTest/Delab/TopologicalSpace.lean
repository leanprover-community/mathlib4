import Mathlib.Topology.Order

open TopologicalSpace
open scoped Topology

-- TODO If and when `(try)SynthInstance` in `#check` is fixed, replace `ℕ` and `Prop` with variables

variable {α : Type*} [TopologicalSpace α] (f : ℕ → α) (p : ℕ → Prop) (s : Set ℕ)

-- For unary ops, we check that `induced p inferInstance` triggers the delab and `inferInstance` does not

/-- info: IsOpen[induced f inferInstance] s ↔ IsOpen s : Prop -/
#guard_msgs(info) in
#check IsOpen[induced f inferInstance] s ↔ IsOpen[inferInstance] s

/-- info: IsClosed[induced f inferInstance] s ↔ IsClosed s : Prop -/
#guard_msgs(info) in
#check IsClosed[induced f inferInstance] s ↔ IsClosed[inferInstance] s

/-- info: closure[induced f inferInstance] s = closure s : Prop -/
#guard_msgs(info) in
#check closure[induced f inferInstance] s = closure[inferInstance] s

-- For binary ops, we check that `(co)induced f inferInstance` in either or both slots triggers the delab
-- and `inferInstance` in both slots does not

/-- info: Continuous[induced f inferInstance, inferInstance] f ↔ Continuous[inferInstance, coinduced f inferInstance] f : Prop -/
#guard_msgs(info) in
#check Continuous[induced f inferInstance, inferInstance] f ↔ Continuous[inferInstance, coinduced f inferInstance] f

/-- info: Continuous[induced p inferInstance, coinduced p inferInstance] p ↔ Continuous p : Prop -/
#guard_msgs(info) in
#check Continuous[induced p inferInstance, coinduced p inferInstance] p ↔ Continuous[inferInstance, inferInstance] p
