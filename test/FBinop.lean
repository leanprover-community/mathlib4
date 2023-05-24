import Mathlib.Tactic.FBinop
import Mathlib.Data.Set.Prod
import Mathlib.Data.Finset.Prod

universe u v w

/-- Notation type class for the set product `×ˢ`. -/
class SProd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- The cartesian product `s ×ˢ t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
  sprod : α → β → γ

-- This notation binds more strongly than (pre)images, unions and intersections.
@[inherit_doc SProd.sprod] infixr:82 " ×ˢ' " => SProd.sprod
macro_rules | `($x ×ˢ' $y)   => `(fbinop% SProd.sprod $x $y)

@[default_instance] instance : SProd (Set α) (Set β) (Set (α × β)) := ⟨Set.prod⟩
instance : SProd (Finset α) (Finset β) (Finset (α × β)) := ⟨Finset.product⟩

-- set_option trace.Elab.fbinop true

example (s : Set α) (t : Set β) : s ×ˢ' t = s ×ˢ' t := rfl
example {α : Type u} {β : Type v} (s : Finset α) (t : Finset β) : s ×ˢ' t = s ×ˢ' t := rfl
example {α : Type u} {β : Type v} (s : Finset α) (t : Set β) : s ×ˢ' t = s ×ˢ' t := rfl

example (f : α × α → β) (s : Set (α × α)) : s.InjOn f := sorry
example (f : α × α → β) (s t : Set α) : (s ×ˢ' t).InjOn f := sorry
example (f : α × α → β) (s t : Finset α) : (s ×ˢ' t : Set (α × α)).InjOn f := sorry
example (f : α × α → β) (s t : Finset α) : (s ×ˢ' t : Set _).InjOn f := sorry
example (f : α × α → β) (s t : Finset α) : ((s : Set _) ×ˢ' (t : Set _)).InjOn f := sorry
example (f : α × α → β) (s t : Finset α) : ((s : Set _) ×ˢ' (t : Set _)).InjOn f := sorry
example (f : α × α → β) (s t : Finset α) : Set.InjOn f (s ×ˢ' t) := sorry

example (s : Set α) (t : Set (α × ℕ)) : s ×ˢ' {n | 0 < n} = t := sorry
example (s : Set α) (t : Set (α × ℕ)) : s ×ˢ' {1, 2, 3} = t := sorry
example (s : Set α) (t : Set (ℕ × α)) : {1, 2, 3} ×ˢ' s = t := sorry
example (s : Finset α) (t : Finset (α × ℕ)) : s ×ˢ' {1, 2, 3} = t := sorry
example (s : Finset α) (t : Finset (ℕ × α)) : {1, 2, 3} ×ˢ' s = t := sorry
example (s : Finset α) (t : Finset (ℕ × α)) : ({1, 2, 3} ×ˢ' s).card = 22 := sorry

axiom Nat.card : Sort u → Nat
example (s : Finset α) (t : Set β) (u : Finset γ) : Nat.card (s ×ˢ' t ×ˢ' u) = 0 := sorry
