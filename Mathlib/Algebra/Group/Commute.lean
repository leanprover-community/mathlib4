/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Semiconj

/-!
# Commuting pairs of elements in monoids

We define the predicate `Commute a b := a * b = b * a` and provide some operations on terms
`(h : Commute a b)`. E.g., if `a`, `b`, and c are elements of a semiring, and that
`hb : Commute a b` and `hc : Commute a c`.  Then `hb.pow_left 5` proves `Commute (a ^ 5) b` and
`(hb.pow_right 2).add_right (hb.mul_right hc)` proves `commute a (b ^ 2 + b * c)`.

Lean does not immediately recognise these terms as equations, so for rewriting we need syntax like
`rw [(hb.pow_left 5).eq]` rather than just `rw [hb.pow_left 5]`.

This file defines only a few operations (`mul_left`, `inv_right`, etc).  Other operations
(`pow_right`, field inverse etc) are in the files that define corresponding notions.

## Implementation details

Most of the proofs come from the properties of `SemiconjBy`.
-/


variable {G : Type _}

/-- Two elements commute if `a * b = b * a`. -/
@[to_additive AddCommute "Two elements additively commute if `a + b = b + a`"]
def Commute {S : Type _} [Mul S] (a b : S) : Prop :=
  SemiconjBy a b b
#align commute Commute
#align add_commute AddCommute

namespace Commute

section Mul

variable {S : Type _} [Mul S]

/-- Equality behind `Commute a b`; useful for rewriting. -/
@[to_additive "Equality behind `add_commute a b`; useful for rewriting."]
protected theorem eq {a b : S} (h : Commute a b) : a * b = b * a :=
  h
#align commute.eq Commute.eq
#align add_commute.eq AddCommute.eq

/-- Any element commutes with itself. -/
@[refl, simp, to_additive "Any element commutes with itself."]
protected theorem refl (a : S) : Commute a a :=
  Eq.refl (a * a)
#align commute.refl Commute.refl
#align add_commute.refl AddCommute.refl

/-- If `a` commutes with `b`, then `b` commutes with `a`. -/
@[symm, to_additive "If `a` commutes with `b`, then `b` commutes with `a`."]
protected theorem symm {a b : S} (h : Commute a b) : Commute b a :=
  Eq.symm h
#align commute.symm Commute.symm
#align add_commute.symm AddCommute.symm

@[to_additive]
protected theorem semiconjBy {a b : S} (h : Commute a b) : SemiconjBy a b b :=
  h
#align commute.semiconj_by Commute.semiconjBy
#align add_commute.semiconj_by AddCommute.semiconjBy

@[to_additive]
protected theorem symm_iff {a b : S} : Commute a b ↔ Commute b a :=
  ⟨Commute.symm, Commute.symm⟩
#align commute.symm_iff Commute.symm_iff
#align add_commute.symm_iff AddCommute.symm_iff

@[to_additive]
instance : IsRefl S Commute :=
  ⟨Commute.refl⟩

-- This instance is useful for `finset.noncomm_prod`
@[to_additive]
instance on_isRefl {f : G → S} : IsRefl G fun a b => Commute (f a) (f b) :=
  ⟨fun _ => Commute.refl _⟩
#align commute.on_is_refl Commute.on_isRefl
#align add_commute.on_is_refl AddCommute.on_isRefl

end Mul

section Semigroup

variable {S : Type _} [Semigroup S] {a b c : S}

/-- If `a` commutes with both `b` and `c`, then it commutes with their product. -/
@[simp, to_additive "If `a` commutes with both `b` and `c`, then it commutes with their sum."]
theorem mul_right (hab : Commute a b) (hac : Commute a c) : Commute a (b * c) :=
  SemiconjBy.mul_right hab hac
#align commute.mul_right Commute.mul_rightₓ
#align add_commute.add_right AddCommute.add_rightₓ
-- I think `ₓ` is necessary because of the `mul` vs `HMul` distinction

/-- If both `a` and `b` commute with `c`, then their product commutes with `c`. -/
@[simp, to_additive "If both `a` and `b` commute with `c`, then their product commutes with `c`."]
theorem mul_left (hac : Commute a c) (hbc : Commute b c) : Commute (a * b) c :=
  SemiconjBy.mul_left hac hbc
#align commute.mul_left Commute.mul_leftₓ
#align add_commute.add_left AddCommute.add_leftₓ
-- I think `ₓ` is necessary because of the `mul` vs `HMul` distinction

@[to_additive]
protected theorem right_comm (h : Commute b c) (a : S) : a * b * c = a * c * b :=
  by simp only [mul_assoc, h.eq]
#align commute.right_comm Commute.right_commₓ
#align add_commute.right_comm AddCommute.right_commₓ
-- I think `ₓ` is necessary because of the `mul` vs `HMul` distinction

@[to_additive]
protected theorem left_comm (h : Commute a b) (c) : a * (b * c) = b * (a * c) :=
  by simp only [← mul_assoc, h.eq]
#align commute.left_comm Commute.left_commₓ
#align add_commute.left_comm AddCommute.left_commₓ
-- I think `ₓ` is necessary because of the `mul` vs `HMul` distinction

end Semigroup

@[to_additive]
protected theorem all {S : Type _} [CommSemigroup S] (a b : S) : Commute a b :=
  mul_comm a b
#align commute.all Commute.allₓ
#align add_commute.all AddCommute.allₓ
-- not sure why this needs an `ₓ`, maybe instance names not aligned?

section MulOneClass

variable {M : Type _} [MulOneClass M]

@[simp, to_additive]
theorem one_right (a : M) : Commute a 1 :=
  SemiconjBy.one_right a
#align commute.one_right Commute.one_rightₓ
#align add_commute.zero_right AddCommute.zero_rightₓ
-- I think `ₓ` is necessary because `One.toOfNat1` appears in the Lean 4 version

@[simp, to_additive]
theorem one_left (a : M) : Commute 1 a :=
  SemiconjBy.one_left a
#align commute.one_left Commute.one_leftₓ
#align add_commute.zero_left AddCommute.zero_leftₓ
-- I think `ₓ` is necessary because `One.toOfNat1` appears in the Lean 4 version

end MulOneClass

section Monoid

variable {M : Type _} [Monoid M] {a b : M} {u u₁ u₂ : Mˣ}

@[simp, to_additive]
theorem pow_right (h : Commute a b) (n : ℕ) : Commute a (b ^ n) :=
  SemiconjBy.pow_right h n
#align commute.pow_right Commute.pow_rightₓ
#align add_commute.smul_right AddCommute.smul_rightₓ
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

@[simp, to_additive]
theorem pow_left (h : Commute a b) (n : ℕ) : Commute (a ^ n) b :=
  (h.symm.pow_right n).symm
#align commute.pow_left Commute.pow_leftₓ
#align add_commute.smul_left AddCommute.smul_leftₓ
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

@[simp, to_additive]
theorem pow_pow (h : Commute a b) (m n : ℕ) : Commute (a ^ m) (b ^ n) :=
  (h.pow_left m).pow_right n
#align commute.pow_pow Commute.pow_powₓ
#align add_commute.smul_smul AddCommute.smul_smulₓ
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

-- porting note: `simpNF` told me to remove the `simp` attribute
@[to_additive]
theorem self_pow (a : M) (n : ℕ) : Commute a (a ^ n) :=
  (Commute.refl a).pow_right n
#align commute.self_pow Commute.self_powₓ
#align add_commute.self_smul AddCommute.self_smulₓ
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

-- porting note: `simpNF` told me to remove the `simp` attribute
@[to_additive]
theorem pow_self (a : M) (n : ℕ) : Commute (a ^ n) a :=
  (Commute.refl a).pow_left n
#align add_commute.smul_self AddCommute.smul_selfₓ
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

-- porting note: `simpNF` told me to remove the `simp` attribute
@[to_additive]
theorem pow_pow_self (a : M) (m n : ℕ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).pow_pow m n
#align commute.pow_pow_self Commute.pow_pow_selfₓ
#align add_commute.smul_smul_self AddCommute.smul_smul_selfₓ
-- `MulOneClass.toHasMul` vs. `MulOneClass.toMul`

@[to_additive succ_nsmul']
theorem _root_.pow_succ' (a : M) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
  (pow_succ a n).trans (self_pow _ _)
#align pow_succ' pow_succ'
#align succ_nsmul' succ_nsmul'

@[to_additive]
theorem units_inv_right : Commute a u → Commute a ↑u⁻¹ :=
  SemiconjBy.units_inv_right
#align commute.units_inv_right Commute.units_inv_right
#align add_commute.add_units_neg_right AddCommute.addUnits_neg_right

@[simp, to_additive]
theorem units_inv_right_iff : Commute a ↑u⁻¹ ↔ Commute a u :=
  SemiconjBy.units_inv_right_iff
#align commute.units_inv_right_iff Commute.units_inv_right_iff
#align add_commute.add_units_neg_right_iff AddCommute.addUnits_neg_right_iff

@[to_additive]
theorem units_inv_left : Commute (↑u) a → Commute (↑u⁻¹) a :=
  SemiconjBy.units_inv_symm_left
#align commute.units_inv_left Commute.units_inv_left
#align add_commute.add_units_neg_left AddCommute.addUnits_neg_left

@[simp, to_additive]
theorem units_inv_left_iff : Commute (↑u⁻¹) a ↔ Commute (↑u) a :=
  SemiconjBy.units_inv_symm_left_iff
#align commute.units_inv_left_iff Commute.units_inv_left_iff
#align add_commute.add_units_neg_left_iff AddCommute.addUnits_neg_left_iff

@[to_additive]
theorem units_val : Commute u₁ u₂ → Commute (u₁ : M) u₂ :=
  SemiconjBy.units_val
#align commute.units_coe Commute.units_val
#align add_commute.add_units_coe AddCommute.addUnits_val

@[to_additive]
theorem units_of_val : Commute (u₁ : M) u₂ → Commute u₁ u₂ :=
  SemiconjBy.units_of_val
#align commute.units_of_coe Commute.units_of_val
#align add_commute.add_units_of_coe AddCommute.addUnits_of_val

@[simp, to_additive]
theorem units_val_iff : Commute (u₁ : M) u₂ ↔ Commute u₁ u₂ :=
  SemiconjBy.units_val_iff
#align commute.units_coe_iff Commute.units_val_iff
#align add_commute.add_units_coe_iff AddCommute.addUnits_val_iff

/-- If the product of two commuting elements is a unit, then the left multiplier is a unit. -/
@[to_additive "If the sum of two commuting elements is an additive unit, then the left summand is
an additive unit."]
def _root_.Units.leftOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ where
  val := a
  inv := b * ↑u⁻¹
  val_inv := by rw [← mul_assoc, hu, u.mul_inv]
  inv_val := by
    have : Commute a u := hu ▸ (Commute.refl _).mul_right hc
    rw [← this.units_inv_right.right_comm, ← hc.eq, hu, u.mul_inv]
#align units.left_of_mul Units.leftOfMul
#align add_units.left_of_add AddUnits.leftOfAdd

/-- If the product of two commuting elements is a unit, then the right multiplier is a unit. -/
@[to_additive "If the sum of two commuting elements is an additive unit, then the right summand
is an additive unit."]
def _root_.Units.rightOfMul (u : Mˣ) (a b : M) (hu : a * b = u) (hc : Commute a b) : Mˣ :=
  u.leftOfMul b a (hc.eq ▸ hu) hc.symm
#align units.right_of_mul Units.rightOfMul
#align add_units.right_of_add AddUnits.rightOfAdd

@[to_additive]
theorem isUnit_mul_iff (h : Commute a b) : IsUnit (a * b) ↔ IsUnit a ∧ IsUnit b :=
  ⟨fun ⟨u, hu⟩ => ⟨(u.leftOfMul a b hu.symm h).isUnit, (u.rightOfMul a b hu.symm h).isUnit⟩,
  fun H => H.1.mul H.2⟩
#align commute.is_unit_mul_iff Commute.isUnit_mul_iff
#align add_commute.is_add_unit_add_iff AddCommute.isAddUnit_add_iff

@[simp, to_additive]
theorem _root_.isUnit_mul_self_iff : IsUnit (a * a) ↔ IsUnit a :=
  (Commute.refl a).isUnit_mul_iff.trans and_self_iff
  -- porting note: `and_self_iff` now has an implicit argument instead of an explicit one.
#align is_unit_mul_self_iff isUnit_mul_self_iff
#align is_add_unit_add_self_iff isAddUnit_add_self_iff

end Monoid

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

@[to_additive]
theorem inv_inv : Commute a b → Commute a⁻¹ b⁻¹ :=
  SemiconjBy.inv_inv_symm
#align commute.inv_inv Commute.inv_inv
#align add_commute.neg_neg AddCommute.neg_neg

@[simp, to_additive]
theorem inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_inv_symm_iff
#align commute.inv_inv_iff Commute.inv_inv_iff
#align add_commute.neg_neg_iff AddCommute.neg_neg_iff

end DivisionMonoid

section Group

variable [Group G] {a b : G}

@[to_additive]
theorem inv_right : Commute a b → Commute a b⁻¹ :=
  SemiconjBy.inv_right
#align commute.inv_right Commute.inv_right
#align add_commute.neg_right AddCommute.neg_right

@[simp, to_additive]
theorem inv_right_iff : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff
#align commute.inv_right_iff Commute.inv_right_iff
#align add_commute.neg_right_iff AddCommute.neg_right_iff

@[to_additive]
theorem inv_left : Commute a b → Commute a⁻¹ b :=
  SemiconjBy.inv_symm_left
#align commute.inv_left Commute.inv_left
#align add_commute.neg_left AddCommute.neg_left

@[simp, to_additive]
theorem inv_left_iff : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff
#align commute.inv_left_iff Commute.inv_left_iff
#align add_commute.neg_left_iff AddCommute.neg_left_iff

@[to_additive]
protected theorem inv_mul_cancel (h : Commute a b) : a⁻¹ * b * a = b := by
  rw [h.inv_left.eq, inv_mul_cancel_right]
#align commute.inv_mul_cancel Commute.inv_mul_cancel
#align add_commute.neg_add_cancel AddCommute.neg_add_cancel

@[to_additive]
theorem inv_mul_cancel_assoc (h : Commute a b) : a⁻¹ * (b * a) = b := by
  rw [← mul_assoc, h.inv_mul_cancel]
#align commute.inv_mul_cancel_assoc Commute.inv_mul_cancel_assoc
#align add_commute.neg_add_cancel_assoc AddCommute.neg_add_cancel_assoc

@[to_additive]
protected theorem mul_inv_cancel (h : Commute a b) : a * b * a⁻¹ = b := by
  rw [h.eq, mul_inv_cancel_right]
#align commute.mul_inv_cancel Commute.mul_inv_cancel
#align add_commute.add_neg_cancel AddCommute.add_neg_cancel

@[to_additive]
theorem mul_inv_cancel_assoc (h : Commute a b) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc, h.mul_inv_cancel]
#align commute.mul_inv_cancel_assoc Commute.mul_inv_cancel_assoc
#align add_commute.add_neg_cancel_assoc AddCommute.add_neg_cancel_assoc

end Group

end Commute

section CommGroup

variable [CommGroup G] (a b : G)

@[simp, to_additive]
theorem mul_inv_cancel_comm : a * b * a⁻¹ = b :=
  (Commute.all a b).mul_inv_cancel
#align mul_inv_cancel_comm mul_inv_cancel_comm
#align add_neg_cancel_comm add_neg_cancel_comm

@[simp, to_additive]
theorem mul_inv_cancel_comm_assoc : a * (b * a⁻¹) = b :=
  (Commute.all a b).mul_inv_cancel_assoc
#align mul_inv_cancel_comm_assoc mul_inv_cancel_comm_assoc
#align add_neg_cancel_comm_assoc add_neg_cancel_comm_assoc

@[simp, to_additive]
theorem inv_mul_cancel_comm : a⁻¹ * b * a = b :=
  (Commute.all a b).inv_mul_cancel
#align inv_mul_cancel_comm inv_mul_cancel_comm
#align neg_add_cancel_comm neg_add_cancel_comm

@[simp, to_additive]
theorem inv_mul_cancel_comm_assoc : a⁻¹ * (b * a) = b :=
  (Commute.all a b).inv_mul_cancel_assoc
#align neg_add_cancel_comm_assoc neg_add_cancel_comm_assoc

end CommGroup
