/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Conjugacy of elements of finite groups
-/

public section

assert_not_exists Field

-- TODO: the following `assert_not_exists` should work, but does not
-- assert_not_exists MonoidWithZero

variable {α : Type*} [Monoid α]

attribute [local instance] IsConj.setoid

instance [Fintype α] [DecidableRel (IsConj : α → α → Prop)] : Fintype (ConjClasses α) :=
  Quotient.fintype (IsConj.setoid α)

instance [Finite α] : Finite (ConjClasses α) :=
  Quotient.finite _

instance [DecidableEq α] [Fintype α] : DecidableRel (IsConj : α → α → Prop) := fun a b =>
  inferInstanceAs (Decidable (∃ c : αˣ, c.1 * a = b * c.1))

instance conjugatesOf.fintype [Fintype α] [DecidableRel (IsConj : α → α → Prop)] {a : α} :
    Fintype (conjugatesOf a) :=
  @Subtype.fintype _ _ (‹DecidableRel IsConj› a) _

namespace ConjClasses

variable [Fintype α] [DecidableRel (IsConj : α → α → Prop)]

instance {x : ConjClasses α} : Fintype (carrier x) :=
  Quotient.recOnSubsingleton x fun _ => conjugatesOf.fintype

section Group

variable {G H : Type*} [Group G] [Fintype G] [DecidableEq G] [CommMonoid H]
  (c : ConjClasses G) (g : G)

/-- Multiplying `f (g * h * g⁻¹)` over `h` in any conjugacy class of `G` equals multiplying
`f h` over `h`. -/
@[to_additive (dont_translate := G) ConjClasses.sum_carrier_mulAut
/-- Summing `f (g * h * g⁻¹)` over `h` in any conjugacy class of `G` equals summing
`f h` over `h`. -/]
theorem prod_carrier_mulAut (f : G → H) :
    ∏ h ∈ c.carrier, f (MulAut.conj g h) =
    ∏ h ∈ c.carrier, f h := by
  rw [← Finset.prod_set_coe, ← Finset.prod_set_coe]
  refine Fintype.prod_equiv (bijOn_conj g _).equiv _ _ fun _ ↦ ?_
  simp [Set.BijOn.equiv]

/-- Multiplying `f (g * h)` over `h` in any conjugacy class of `G` equals multiplying
`f (h * g)` over `h`. -/
@[to_additive (dont_translate := G) ConjClasses.sum_carrier_mul_left
/-- Summing `f (g * h)` over `h` in any conjugacy class of `G` equals summing
`f (h * g)` over `h`. -/]
theorem prod_carrier_mul_left (f : G → H) :
    ∏ h ∈ c.carrier, f (g * h) =
    ∏ h ∈ c.carrier, f (h * g) := by
  rw [← Finset.prod_set_coe, ← Finset.prod_set_coe]
  refine Fintype.prod_equiv (bijOn_conj g _).equiv _ _ fun _ ↦ ?_
  simp [Set.BijOn.equiv]

end Group

end ConjClasses
