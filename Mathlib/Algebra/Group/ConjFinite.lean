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

variable {G M : Type*} [Group G] [Fintype G] [DecidableEq G] [CommMonoid M]
  (c : ConjClasses G) (g : G) (f : G → M)

/-- Multiplying `f (g * h * g⁻¹)` over `h` in any conjugacy class of `G` equals multiplying
`f h` over `h`. -/
@[to_additive (dont_translate := G) ConjClasses.sum_carrier_conj
/-- Summing `f (g * h * g⁻¹)` over `h` in any conjugacy class of `G` equals summing
`f h` over `h`. -/]
theorem prod_carrier_conj :
    ∏ h ∈ c.carrier, f (MulAut.conj g h) = ∏ h ∈ c.carrier, f h :=
  have := c.carrier.coe_toFinset ▸ (invOn_conj ..).bijOn (mapsTo_conj ..) (mapsTo_conj ..)
  Finset.prod_nbij (MulAut.conj g) this.mapsTo this.injOn this.surjOn (by simp)

/-- Multiplying `f (g * h)` over `h` in any conjugacy class of `G` equals multiplying
`f (h * g)` over `h`. -/
@[to_additive (dont_translate := G) ConjClasses.sum_carrier_mul_left
/-- Summing `f (g * h)` over `h` in any conjugacy class of `G` equals summing
`f (h * g)` over `h`. -/]
theorem prod_carrier_mul_left :
    ∏ h ∈ c.carrier, f (g * h) = ∏ h ∈ c.carrier, f (h * g) :=
  have := c.carrier.coe_toFinset ▸ (invOn_conj ..).bijOn (mapsTo_conj ..) (mapsTo_conj ..)
  Finset.prod_nbij (MulAut.conj g) this.mapsTo this.injOn this.surjOn (by simp)

end Group

end ConjClasses
