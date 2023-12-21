/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Semiconj.Units

#align_import algebra.group.commute from "leanprover-community/mathlib"@"05101c3df9d9cfe9430edc205860c79b6d660102"

/-!
# Lemmas about commuting pairs of elements involving units.

-/


variable {G : Type*}

namespace Commute

section Monoid

variable {M : Type*} [Monoid M] {a b : M} {u u₁ u₂ : Mˣ}

@[to_additive]
theorem units_inv_right : Commute a u → Commute a ↑u⁻¹ :=
  SemiconjBy.units_inv_right
#align commute.units_inv_right Commute.units_inv_right
#align add_commute.add_units_neg_right AddCommute.addUnits_neg_right

@[to_additive (attr := simp)]
theorem units_inv_right_iff : Commute a ↑u⁻¹ ↔ Commute a u :=
  SemiconjBy.units_inv_right_iff
#align commute.units_inv_right_iff Commute.units_inv_right_iff
#align add_commute.add_units_neg_right_iff AddCommute.addUnits_neg_right_iff

@[to_additive]
theorem units_inv_left : Commute (↑u) a → Commute (↑u⁻¹) a :=
  SemiconjBy.units_inv_symm_left
#align commute.units_inv_left Commute.units_inv_left
#align add_commute.add_units_neg_left AddCommute.addUnits_neg_left

@[to_additive (attr := simp)]
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

@[to_additive (attr := simp)]
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

@[to_additive (attr := simp)]
theorem _root_.isUnit_mul_self_iff : IsUnit (a * a) ↔ IsUnit a :=
  (Commute.refl a).isUnit_mul_iff.trans (and_self_iff _)
  -- porting note: `and_self_iff` now has an implicit argument instead of an explicit one.
#align is_unit_mul_self_iff isUnit_mul_self_iff
#align is_add_unit_add_self_iff isAddUnit_add_self_iff

end Monoid

section Group

variable [Group G] {a b : G}

@[to_additive]
theorem inv_right : Commute a b → Commute a b⁻¹ :=
  SemiconjBy.inv_right
#align commute.inv_right Commute.inv_right
#align add_commute.neg_right AddCommute.neg_right

@[to_additive (attr := simp)]
theorem inv_right_iff : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff
#align commute.inv_right_iff Commute.inv_right_iff
#align add_commute.neg_right_iff AddCommute.neg_right_iff

@[to_additive]
theorem inv_left : Commute a b → Commute a⁻¹ b :=
  SemiconjBy.inv_symm_left
#align commute.inv_left Commute.inv_left
#align add_commute.neg_left AddCommute.neg_left

@[to_additive (attr := simp)]
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

end Group

end Commute

section CommGroup

variable [CommGroup G] (a b : G)

@[to_additive (attr := simp)]
theorem inv_mul_cancel_comm : a⁻¹ * b * a = b :=
  (Commute.all a b).inv_mul_cancel
#align inv_mul_cancel_comm inv_mul_cancel_comm
#align neg_add_cancel_comm neg_add_cancel_comm

@[to_additive (attr := simp)]
theorem inv_mul_cancel_comm_assoc : a⁻¹ * (b * a) = b :=
  (Commute.all a b).inv_mul_cancel_assoc
#align inv_mul_cancel_comm_assoc inv_mul_cancel_comm_assoc
#align neg_add_cancel_comm_assoc neg_add_cancel_comm_assoc

end CommGroup
