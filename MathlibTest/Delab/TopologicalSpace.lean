import Mathlib.Topology.Order

open TopologicalSpace
open scoped Topology

-- TODO If and when `(try)SynthInstance` in `#check` is fixed, replace `ℕ` and `Prop` with variables

variable {α β : Type*} [TopologicalSpace α]
  (f : ℕ → α) (g : β → α) (h : α → β) (p : ℕ → Prop)
  (s : Set ℕ) (t : Set β)

section unary

section applied

-- For unary ops, we check that `induced f inferInstance` (not the canonical `TopologicalSpace ℕ`)
-- and `induced g inferInstance` (`β` has no `TopologicalSpace` instance) trigger the delab and
-- `inferInstance` does not

/-- info:
[IsOpen[induced f inferInstance] s, IsOpen[induced g inferInstance] t, IsOpen s] : List Prop -/
#guard_msgs(info) in
#check [IsOpen[induced f inferInstance] s, IsOpen[induced g inferInstance] t,
  IsOpen[inferInstance] s]

/-- info:
[IsClosed[induced f inferInstance] s, IsClosed[induced g inferInstance] t,
IsClosed s] : List Prop -/
#guard_msgs(info) in
#check [IsClosed[induced f inferInstance] s, IsClosed[induced g inferInstance] t,
  IsClosed[inferInstance] s]

/-- info:
[closure[induced f inferInstance] s, closure s] : List (Set ℕ) -/
#guard_msgs(info) in
#check [closure[induced f inferInstance] s, closure[inferInstance] s]

/-- info: closure[induced g inferInstance] t : Set β -/
#guard_msgs(info) in
#check closure[induced g inferInstance] t

end applied

section unapplied

-- Same as above, except with unapplied operators.

/-- info: [IsOpen[induced f inferInstance], IsOpen] : List (Set ℕ → Prop) -/
#guard_msgs(info) in
#check [IsOpen[induced f inferInstance], IsOpen[inferInstance]]

/-- info: IsOpen[induced g inferInstance] : Set β → Prop -/
#guard_msgs(info) in
#check IsOpen[induced g inferInstance]


/-- info: [IsClosed[induced f inferInstance], IsClosed] : List (Set ℕ → Prop) -/
#guard_msgs(info) in
#check [IsClosed[induced f inferInstance], IsClosed[inferInstance]]

/-- info: IsClosed[induced g inferInstance] : Set β → Prop -/
#guard_msgs(info) in
#check IsClosed[induced g inferInstance]

/-- info: [closure[induced f inferInstance], closure] : List (Set ℕ → Set ℕ) -/
#guard_msgs(info) in
#check [closure[induced f inferInstance], closure[inferInstance]]

/-- info: closure[induced g inferInstance] : Set β → Set β -/
#guard_msgs(info) in
#check closure[induced g inferInstance]

end unapplied
end unary

section binary

section applied

-- For binary ops, we check that
-- `(co)induced f inferInstance` (not the canonical instance on `ℕ`/`α`) and
-- `induced g inferInstance` and `coinduced h inferInstance` (no instance on `β`)
-- in either or both slots do trigger the delab and that `inferInstance` in both slots does not

/-- info: [Continuous[induced f inferInstance, inferInstance] f,
Continuous[induced g inferInstance, inferInstance] g,
  Continuous[inferInstance, coinduced f inferInstance] f,
Continuous[inferInstance, coinduced h inferInstance] h,
  Continuous[induced p inferInstance, coinduced p inferInstance] p,
Continuous p] : List Prop -/
#guard_msgs(info) in
#check [Continuous[induced f inferInstance, inferInstance] f,
  Continuous[induced g inferInstance, inferInstance] g,
  Continuous[inferInstance, coinduced f inferInstance] f,
  Continuous[inferInstance, coinduced h inferInstance] h,
  Continuous[induced p inferInstance, coinduced p inferInstance] p,
  Continuous[inferInstance, inferInstance] p]

end applied

section unapplied

-- Same as above, except for unapplied operators.

/-- info: [Continuous[induced p inferInstance, inferInstance],
Continuous[inferInstance, coinduced p inferInstance],
  Continuous[induced p inferInstance, coinduced p inferInstance],
Continuous] : List ((ℕ → Prop) → Prop) -/
#guard_msgs(info) in
#check [Continuous[induced p inferInstance, inferInstance],
  Continuous[inferInstance, coinduced p inferInstance],
  Continuous[induced p inferInstance, coinduced p inferInstance],
  Continuous[inferInstance, inferInstance]]

/-- info:
Continuous[induced g inferInstance, inferInstanceAs (TopologicalSpace α)] : (β → α) → Prop -/
#guard_msgs(info) in
#check Continuous[induced g inferInstance, inferInstanceAs (TopologicalSpace α)]

/-- info:
Continuous[inferInstanceAs (TopologicalSpace α), coinduced h inferInstance] : (α → β) → Prop -/
#guard_msgs(info) in
#check Continuous[inferInstanceAs (TopologicalSpace α), coinduced h inferInstance]

end unapplied
end binary
