/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Semiconj.Basic

#align_import algebra.group.commute from "leanprover-community/mathlib"@"05101c3df9d9cfe9430edc205860c79b6d660102"

/-!
# Additional lemmas about commuting pairs of elements in monoids

-/

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

variable {G : Type*}

namespace Commute

section DivisionMonoid

variable [DivisionMonoid G] {a b c d: G}

@[to_additive]
protected theorem inv_inv : Commute a b → Commute a⁻¹ b⁻¹ :=
  SemiconjBy.inv_inv_symm
#align commute.inv_inv Commute.inv_inv
#align add_commute.neg_neg AddCommute.neg_neg

@[to_additive (attr := simp)]
theorem inv_inv_iff : Commute a⁻¹ b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_inv_symm_iff
#align commute.inv_inv_iff Commute.inv_inv_iff
#align add_commute.neg_neg_iff AddCommute.neg_neg_iff

@[to_additive]
protected theorem div_mul_div_comm (hbd : Commute b d) (hbc : Commute b⁻¹ c) :
    a / b * (c / d) = a * c / (b * d) := by
  simp_rw [div_eq_mul_inv, mul_inv_rev, hbd.inv_inv.symm.eq, hbc.mul_mul_mul_comm]
#align commute.div_mul_div_comm Commute.div_mul_div_comm
#align add_commute.sub_add_sub_comm AddCommute.sub_add_sub_comm

@[to_additive]
protected theorem mul_div_mul_comm (hcd : Commute c d) (hbc : Commute b c⁻¹) :
    a * b / (c * d) = a / c * (b / d) :=
  (hcd.div_mul_div_comm hbc.symm).symm
#align commute.mul_div_mul_comm Commute.mul_div_mul_comm
#align add_commute.add_sub_add_comm AddCommute.add_sub_add_comm

@[to_additive]
protected theorem div_div_div_comm (hbc : Commute b c) (hbd : Commute b⁻¹ d) (hcd : Commute c⁻¹ d) :
    a / b / (c / d) = a / c / (b / d) := by
  simp_rw [div_eq_mul_inv, mul_inv_rev, inv_inv, hbd.symm.eq, hcd.symm.eq,
    hbc.inv_inv.mul_mul_mul_comm]
#align commute.div_div_div_comm Commute.div_div_div_comm
#align add_commute.sub_sub_sub_comm AddCommute.sub_sub_sub_comm

end DivisionMonoid

section Group
variable [Group G] {a b : G}

@[to_additive (attr := simp)]
lemma inv_left_iff : Commute a⁻¹ b ↔ Commute a b := SemiconjBy.inv_symm_left_iff
#align commute.inv_left_iff Commute.inv_left_iff
#align add_commute.neg_left_iff AddCommute.neg_left_iff

@[to_additive] alias ⟨_, inv_left⟩ := inv_left_iff
#align commute.inv_left Commute.inv_left
#align add_commute.neg_left AddCommute.neg_left

@[to_additive (attr := simp)]
lemma inv_right_iff : Commute a b⁻¹ ↔ Commute a b := SemiconjBy.inv_right_iff
#align commute.inv_right_iff Commute.inv_right_iff
#align add_commute.neg_right_iff AddCommute.neg_right_iff

@[to_additive] alias ⟨_, inv_right⟩ := inv_right_iff
#align commute.inv_right Commute.inv_right
#align add_commute.neg_right AddCommute.neg_right

@[to_additive]
protected lemma inv_mul_cancel (h : Commute a b) : a⁻¹ * b * a = b := by
  rw [h.inv_left.eq, inv_mul_cancel_right]
#align commute.inv_mul_cancel Commute.inv_mul_cancel
#align add_commute.neg_add_cancel AddCommute.neg_add_cancel

@[to_additive]
lemma inv_mul_cancel_assoc (h : Commute a b) : a⁻¹ * (b * a) = b := by
  rw [← mul_assoc, h.inv_mul_cancel]
#align commute.inv_mul_cancel_assoc Commute.inv_mul_cancel_assoc
#align add_commute.neg_add_cancel_assoc AddCommute.neg_add_cancel_assoc

@[to_additive (attr := simp)]
protected theorem conj_iff (h : G) : Commute (h * a * h⁻¹) (h * b * h⁻¹) ↔ Commute a b :=
  SemiconjBy.conj_iff

@[to_additive]
protected theorem conj (comm : Commute a b) (h : G) : Commute (h * a * h⁻¹) (h * b * h⁻¹) :=
  (Commute.conj_iff h).mpr comm

@[to_additive (attr := simp)]
lemma zpow_right (h : Commute a b) (m : ℤ) : Commute a (b ^ m) := SemiconjBy.zpow_right h m
#align commute.zpow_right Commute.zpow_right
#align add_commute.zsmul_right AddCommute.zsmul_right

@[to_additive (attr := simp)]
lemma zpow_left (h : Commute a b) (m : ℤ) : Commute (a ^ m) b := (h.symm.zpow_right m).symm
#align commute.zpow_left Commute.zpow_left
#align add_commute.zsmul_left AddCommute.zsmul_left

@[to_additive] lemma zpow_zpow (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left m).zpow_right n
#align commute.zpow_zpow Commute.zpow_zpow
#align add_commute.zsmul_zsmul AddCommute.zsmul_zsmul

variable (a) (m n : ℤ)

@[to_additive] lemma self_zpow : Commute a (a ^ n) := (Commute.refl a).zpow_right n
#align commute.self_zpow Commute.self_zpow
#align add_commute.self_zsmul AddCommute.self_zsmul

@[to_additive] lemma zpow_self : Commute (a ^ n) a := (Commute.refl a).zpow_left n
#align commute.zpow_self Commute.zpow_self
#align add_commute.zsmul_self AddCommute.zsmul_self

@[to_additive] lemma zpow_zpow_self : Commute (a ^ m) (a ^ n) := (Commute.refl a).zpow_zpow m n
#align commute.zpow_zpow_self Commute.zpow_zpow_self
#align add_commute.zsmul_zsmul_self AddCommute.zsmul_zsmul_self

end Group
end Commute

section Group
variable [Group G]

@[to_additive] lemma pow_inv_comm (a : G) (m n : ℕ) : a⁻¹ ^ m * a ^ n = a ^ n * a⁻¹ ^ m :=
  (Commute.refl a).inv_left.pow_pow _ _
#align pow_inv_comm pow_inv_comm
#align nsmul_neg_comm nsmul_neg_comm

end Group
