import Mathlib.Tactic.FBinop
import Mathlib.Data.Set.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Data.SetLike.Basic

universe u v w

/-- Notation type class for the set product `×ˢ`. -/
class SProd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- The cartesian product `s ×ˢ t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
  sprod : α → β → γ

-- This notation binds more strongly than (pre)images, unions and intersections.
@[inherit_doc SProd.sprod] infixr:82 " ×ˢ' " => SProd.sprod
macro_rules | `($x ×ˢ' $y)   => `(fbinop% SProd.sprod $x $y)

@[default_instance]
instance : SProd (Set α) (Set β) (Set (α × β)) := ⟨Set.prod⟩
instance : SProd (Finset α) (Finset β) (Finset (α × β)) := ⟨Finset.product⟩

set_option trace.Elab.fbinop true

-- These work without `fbinop%`. They're tests that we haven't broken anything.

example (s : Set α) (t : Set β) : s ×ˢ' t = s ×ˢ' t := rfl
example {α : Type u} {β : Type v} (s : Finset α) (t : Finset β) : s ×ˢ' t = s ×ˢ' t := rfl

example (f : α × α → β) (s : Set (α × α)) : s.InjOn f := sorry
example (f : α × α → β) (s t : Set α) : (s ×ˢ' t).InjOn f := sorry
example (f : α × α → β) (s t : Finset α) : (s ×ˢ' t : Set (α × α)).InjOn f := sorry
example (f : α × α → β) (s t : Finset α) : (s ×ˢ' t : Set _).InjOn f := sorry
example (f : α × α → β) (s t : Finset α) : (s ×ˢ' t : Set _).InjOn f := sorry
example (f : α × α → β) (s t : Finset α) : ((s : Set _) ×ˢ' (t : Set _)).InjOn f := sorry
example (f : α × α → β) (s t : Finset α) : ((s : Set _) ×ˢ' (t : Set _)).InjOn f := sorry
example (f : α × α → β) (s t : Finset α) : Set.InjOn f (s ×ˢ' t) := sorry

axiom Nat.card : Sort u → Nat
example (s : Finset α) (t : Finset γ) : Nat.card (s ×ˢ' t) = 0 := sorry

example (s : Set α) (t : Set (α × ℕ)) : s ×ˢ' {n | 0 < n} = t := sorry
example (s : Set α) (t : Set (α × ℕ)) : s ×ˢ' {1, 2, 3} = t := sorry
example (s : Set α) (t : Set (ℕ × α)) : {1, 2, 3} ×ˢ' s = t := sorry

-- These need `fbinop%`.

example {α : Type u} {β : Type v} (s : Finset α) (t : Set β) : s ×ˢ' t = s ×ˢ' t := rfl
example (s : Finset α) (t : Finset (α × ℕ)) : s ×ˢ' {1, 2, 3} = t := sorry
example (s : Finset α) (t : Finset (ℕ × α)) : {1, 2, 3} ×ˢ' s = t := sorry
example (s : Finset α) (t : Finset (ℕ × α)) : ({1, 2, 3} ×ˢ' s).card = 22 := sorry

example (s : Finset α) (t : Set β) (u : Finset γ) : Nat.card (s ×ˢ' t ×ˢ' u) = 0 := sorry

example (s : Finset α) (t : Finset β) :
    (↑(s ×ˢ' t) : Set _) = (s : Set α) ×ˢ' t := Finset.coe_product s t

structure SubObj (X : Type _) where
  carrier : Set X

instance : SetLike (SubObj X) X
    where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr

-- Note: this only works because the last argument of `SubObj` is a type.
-- For other algebra subobjects, an instance argument comes next -- perhaps we should strip
-- these off in the calculation?
def SubObj.prod (s : SubObj X) (t : SubObj Y) : SubObj (X × Y) where
  carrier := s ×ˢ' t
