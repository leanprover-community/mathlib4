import Mathlib.Topology.Order

open TopologicalSpace
open scoped Topology

variable (p : ℕ → Prop) (s : Set ℕ)

-- For unary ops, we check that `induced p inferInstance` triggers the delab and `inferInstance` does not

/-- info: IsOpen[induced p inferInstance] s ↔ IsOpen s : Prop -/
#guard_msgs(info) in
#check IsOpen[induced p inferInstance] s ↔ IsOpen[inferInstance] s

/-- info: IsClosed[induced p inferInstance] s ↔ IsClosed s : Prop -/
#guard_msgs(info) in
#check IsClosed[induced p inferInstance] s ↔ IsClosed[inferInstance] s

/-- info: closure[induced p inferInstance] s = closure s : Prop -/
#guard_msgs(info) in
#check closure[induced p inferInstance] s = closure[inferInstance] s

/-- info: Continuous[induced p inferInstance, inferInstance] p ↔ Continuous[inferInstance, coinduced p inferInstance] p : Prop -/
#guard_msgs(info) in
#check Continuous[induced p inferInstance, inferInstance] p ↔ Continuous[inferInstance, coinduced p inferInstance] p

-- For binary ops, we check that `(co)induced p inferInstance` in either or both slots triggers the delab
-- and `inferInstance` in both slots does not

/-- info: Continuous[induced p inferInstance, inferInstance] p ↔ Continuous[inferInstance, coinduced p inferInstance] p : Prop -/
#guard_msgs(info) in
#check Continuous[induced p inferInstance, inferInstance] p ↔ Continuous[inferInstance, coinduced p inferInstance] p

/-- info: Continuous[induced p inferInstance, coinduced p inferInstance] p ↔ Continuous p : Prop -/
#guard_msgs(info) in
#check Continuous[induced p inferInstance, coinduced p inferInstance] p ↔ Continuous[inferInstance, inferInstance] p
