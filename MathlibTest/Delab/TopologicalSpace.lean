import Mathlib.Topology.Order

open TopologicalSpace

-- TODO If and when `(try)SynthInstance` in `#check` is fixed,
-- replace `ℕ` and `Prop` with variables

variable {α β : Type*} [TopologicalSpace α]
  {τ₁ τ₂ : TopologicalSpace ℕ} {σ₁ σ₂ : TopologicalSpace Prop}
  (f : ℕ → α) (g : β → α) (h : α → β) (p : ℕ → Prop)
  (s : Set ℕ) (t : Set β)

section

-- Delab should not trigger when `Topology` scope is not open

section applied

/-- info: [IsOpen s, IsClosed s, Continuous p, Continuous p] : List Prop -/
#guard_msgs(info) in
#check [@IsOpen _ (induced f inferInstance) s, @IsClosed _ (induced f inferInstance) s,
  @Continuous _ _ (induced p inferInstance) _ p, @Continuous _ _ _ (coinduced p inferInstance) p]

/-- info: closure s : Set ℕ -/
#guard_msgs(info) in
#check @closure _ (induced f inferInstance) s

end applied

section unapplied

/-- info: [IsOpen, IsClosed] : List (Set ℕ → Prop) -/
#guard_msgs(info) in
#check [@IsOpen _ (induced f inferInstance), @IsClosed _ (induced f inferInstance)]

/-- info: closure : Set ℕ → Set ℕ -/
#guard_msgs(info) in
#check @closure _ (induced f inferInstance)

/-- info: [Continuous, Continuous] : List ((ℕ → Prop) → Prop) -/
#guard_msgs(info) in
#check [@Continuous _ _ (induced p inferInstance) _, @Continuous _ _ _ (coinduced p inferInstance)]

end unapplied
end

open scoped Topology
section unary

section applied

-- For unary ops, we check that
-- `τ₁`, `τ₂`, (multiple noncanonical `TopologicalSpace ℕ` instances)
-- and `induced g inferInstance` (`β` has no `TopologicalSpace` instance) trigger the delab and
-- `instTopologicalSpaceNat` does not.
-- (Note that, if there are extra instances of `TopologicalSpace _` lying around, `inferInstance`
-- prioritizes the local variable over the canonical instance.)

/-- info: [IsOpen[τ₁] s, IsOpen[τ₂] s, IsOpen[induced g inferInstance] t, IsOpen s] : List Prop -/
#guard_msgs(info) in
#check [IsOpen[τ₁] s, IsOpen[τ₂] s, IsOpen[induced g inferInstance] t,
IsOpen[instTopologicalSpaceNat] s]

/-- info:
[IsClosed[τ₁] s, IsClosed[τ₂] s, IsClosed[induced g inferInstance] t, IsClosed s] : List Prop -/
#guard_msgs(info) in
#check [IsClosed[τ₁] s, IsClosed[τ₂] s, IsClosed[induced g inferInstance] t,
IsClosed[instTopologicalSpaceNat] s]

/-- info: [closure[τ₁] s, closure[τ₂] s, closure s] : List (Set ℕ) -/
#guard_msgs(info) in
#check [closure[τ₁] s, closure[τ₂] s, closure[instTopologicalSpaceNat] s]

/-- info: closure[induced g inferInstance] t : Set β -/
#guard_msgs(info) in
#check closure[induced g inferInstance] t

end applied

section unapplied

-- Same as above, except with unapplied operators.

/-- info: [IsOpen[τ₁], IsOpen[τ₂], IsOpen] : List (Set ℕ → Prop) -/
#guard_msgs(info) in
#check [IsOpen[τ₁], IsOpen[τ₂], IsOpen[instTopologicalSpaceNat]]

/-- info: IsOpen[induced g inferInstance] : Set β → Prop -/
#guard_msgs(info) in
#check IsOpen[induced g inferInstance]

/-- info: [IsClosed[τ₁], IsClosed[τ₂], IsClosed]
: List (Set ℕ → Prop) -/
#guard_msgs(info) in
#check [IsClosed[τ₁], IsClosed[τ₂], IsClosed[instTopologicalSpaceNat]]

/-- info: IsClosed[induced g inferInstance] : Set β → Prop -/
#guard_msgs(info) in
#check IsClosed[induced g inferInstance]

/-- info: [closure[τ₁], closure[τ₂], closure] : List (Set ℕ → Set ℕ) -/
#guard_msgs(info) in
#check [closure[τ₁], closure[τ₂], closure[instTopologicalSpaceNat]]

/-- info: closure[induced g inferInstance] : Set β → Set β -/
#guard_msgs(info) in
#check closure[induced g inferInstance]

end unapplied
end unary

section binary

section applied

-- For binary ops, we check each argument separately: that is,
-- `τ₁, τ₂`, `σ₁, σ₂` (multiple canonical instances on `ℕ`/`Prop`) and
-- `induced g inferInstance` and `coinduced h inferInstance` (no instance on `β`)
-- in either or both slots do trigger the delab and that
-- `instTopologicalSpaceNat`, `sierpinskiSpace` does not.

/-- info: [Continuous[τ₁, sierpinskiSpace] p, Continuous[τ₂, sierpinskiSpace] p,
  Continuous[induced g inferInstance, inferInstance] g] : List Prop -/
#guard_msgs(info) in
#check [Continuous[τ₁, sierpinskiSpace] p, Continuous[τ₂, sierpinskiSpace] p,
  Continuous[induced g inferInstance, inferInstance] g]

/-- info: [Continuous[instTopologicalSpaceNat, σ₁] p, Continuous[instTopologicalSpaceNat, σ₂] p,
  Continuous[inferInstance, coinduced h inferInstance] h] : List Prop -/
#guard_msgs(info) in
#check [Continuous[instTopologicalSpaceNat, σ₁] p, Continuous[instTopologicalSpaceNat, σ₂] p,
  Continuous[inferInstance, coinduced h inferInstance] h]

/-- info: [Continuous[induced p inferInstance, coinduced p inferInstance] p, Continuous p]
: List Prop -/
#guard_msgs(info) in
#check [Continuous[induced p inferInstance, coinduced p inferInstance] p,
  Continuous[instTopologicalSpaceNat, sierpinskiSpace] p]

end applied

section unapplied

-- Same as above, except for unapplied operators.

/-- info: [Continuous[τ₁, sierpinskiSpace], Continuous[τ₂, sierpinskiSpace]]
: List ((ℕ → Prop) → Prop) -/
#guard_msgs(info) in
#check [Continuous[τ₁, sierpinskiSpace], Continuous[τ₂, sierpinskiSpace]]

/-- info:
Continuous[induced g inferInstance, inferInstanceAs (TopologicalSpace α)] : (β → α) → Prop -/
#guard_msgs(info) in
#check Continuous[induced g inferInstance, inferInstanceAs (TopologicalSpace α)]

/-- info: [Continuous[instTopologicalSpaceNat, σ₁], Continuous[instTopologicalSpaceNat, σ₂]]
: List ((ℕ → Prop) → Prop) -/
#guard_msgs(info) in
#check [Continuous[instTopologicalSpaceNat, σ₁], Continuous[instTopologicalSpaceNat, σ₂]]

/-- info:
Continuous[inferInstanceAs (TopologicalSpace α), coinduced h inferInstance] : (α → β) → Prop -/
#guard_msgs(info) in
#check Continuous[inferInstanceAs (TopologicalSpace α), coinduced h inferInstance]

/-- info: [Continuous[induced p inferInstance, coinduced p inferInstance], Continuous]
: List ((ℕ → Prop) → Prop) -/
#guard_msgs(info) in
#check [Continuous[induced p inferInstance, coinduced p inferInstance],
  Continuous[instTopologicalSpaceNat, sierpinskiSpace]]

end unapplied
end binary
