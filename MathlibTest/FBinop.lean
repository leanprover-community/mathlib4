import Mathlib.Tactic.FBinop
import Mathlib.Data.Set.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Data.SetLike.Basic

private axiom test_sorry : ∀ {α}, α
universe u v w
set_option autoImplicit true

namespace FBinopTests

/-- Notation type class for the set product `×ˢ`. -/
class SProd' (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /-- The Cartesian product `s ×ˢ t` is the set of `(a, b)` such that `a ∈ s` and `b ∈ t`. -/
  sprod : α → β → γ

-- This notation binds more strongly than (pre)images, unions and intersections.
@[inherit_doc SProd'.sprod] infixr:82 " ×ˢ' " => SProd'.sprod
macro_rules | `($x ×ˢ' $y)   => `(fbinop% SProd'.sprod $x $y)

@[default_instance]
instance : SProd' (Set α) (Set β) (Set (α × β)) := ⟨Set.prod⟩
instance : SProd' (Finset α) (Finset β) (Finset (α × β)) := ⟨Finset.product⟩

-- set_option trace.Elab.fbinop true

-- These work without `fbinop%`. They're tests that we haven't broken anything.

example (s : Set α) (t : Set β) : s ×ˢ' t = s ×ˢ' t := rfl
example {α : Type u} {β : Type v} (s : Finset α) (t : Finset β) : s ×ˢ' t = s ×ˢ' t := rfl

example (f : α × α → β) (s : Set (α × α)) : s.InjOn f := test_sorry
example (f : α × α → β) (s t : Set α) : (s ×ˢ' t).InjOn f := test_sorry
example (f : α × α → β) (s t : Finset α) : (s ×ˢ' t : Set (α × α)).InjOn f := test_sorry
example (f : α × α → β) (s t : Finset α) : (s ×ˢ' t : Set _).InjOn f := test_sorry
example (f : α × α → β) (s t : Finset α) : (s ×ˢ' t : Set _).InjOn f := test_sorry
example (f : α × α → β) (s t : Finset α) : ((s : Set _) ×ˢ' (t : Set _)).InjOn f := test_sorry
example (f : α × α → β) (s t : Finset α) : ((s : Set _) ×ˢ' (t : Set _)).InjOn f := test_sorry
example (f : α × α → β) (s t : Finset α) : Set.InjOn f (s ×ˢ' t) := test_sorry

axiom Nat.card : Sort u → Nat
example (s : Finset α) (t : Finset γ) : Nat.card (s ×ˢ' t) = 0 := test_sorry

example (s : Set α) (t : Set (α × ℕ)) : s ×ˢ' {n | 0 < n} = t := test_sorry
example (s : Set α) (t : Set (α × ℕ)) : s ×ˢ' {1, 2, 3} = t := test_sorry
example (s : Set α) (t : Set (ℕ × α)) : {1, 2, 3} ×ˢ' s = t := test_sorry

-- These need `fbinop%`. (Comment out `macro_rules` above to check.)

example {α : Type u} {β : Type v} (s : Finset α) (t : Set β) : s ×ˢ' t = s ×ˢ' t := rfl
example (s : Finset α) (t : Finset (α × ℕ)) : s ×ˢ' {1, 2, 3} = t := test_sorry
example (s : Finset α) (t : Finset (ℕ × α)) : {1, 2, 3} ×ˢ' s = t := test_sorry
example (s : Finset α) (_t : Finset (ℕ × α)) : ({1, 2, 3} ×ˢ' s).card = 22 := test_sorry

/--
info: {1, 2, 3} ×ˢ' {4, 5, 6} : Finset (ℕ × ℕ)
-/
#guard_msgs in
#check ({1,2,3} ×ˢ' {4,5,6} : Finset _)

example (s : Finset α) (t : Set β) (u : Finset γ) : Nat.card (s ×ˢ' t ×ˢ' u) = 0 := test_sorry

example (s : Finset α) (t : Finset β) :
    (↑(s ×ˢ' t) : Set _) = (s : Set α) ×ˢ' t := Finset.coe_product s t

structure SubObj (X : Type _) where
  carrier : Set X

instance : SetLike (SubObj X) X where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr

-- Note: this easily works because the last argument of `SubObj` is a type.
def SubObj.prod (s : SubObj X) (t : SubObj Y) : SubObj (X × Y) where
  carrier := s ×ˢ' t

/-- Modeling subobjects of algebraic types, which have an instance argument after the type. -/
structure DecSubObj (X : Type _) [DecidableEq X] where
  carrier : Set X

instance [DecidableEq X] : SetLike (DecSubObj X) X where
  coe s := s.carrier
  coe_injective' p q h := by cases p; cases q; congr

-- Note: this is testing instance arguments after the type.
def DecSubObj.prod [DecidableEq X] [DecidableEq Y] (s : DecSubObj X) (t : DecSubObj Y) :
    DecSubObj (X × Y) where
  carrier := s ×ˢ' t

end FBinopTests
