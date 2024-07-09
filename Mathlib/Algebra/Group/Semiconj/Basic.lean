/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Group.Basic

#align_import algebra.group.semiconj from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Lemmas about semiconjugate elements of a group

-/

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

namespace SemiconjBy
variable {G : Type*}

section DivisionMonoid
variable [DivisionMonoid G] {a x y : G}

@[to_additive (attr := simp)]
theorem inv_inv_symm_iff : SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔ SemiconjBy a y x := by
  simp_rw [SemiconjBy, ← mul_inv_rev, inv_inj, eq_comm]
#align semiconj_by.inv_inv_symm_iff SemiconjBy.inv_inv_symm_iff
#align add_semiconj_by.neg_neg_symm_iff AddSemiconjBy.neg_neg_symm_iff

@[to_additive] alias ⟨_, inv_inv_symm⟩ := inv_inv_symm_iff
#align semiconj_by.inv_inv_symm SemiconjBy.inv_inv_symm
#align add_semiconj_by.neg_neg_symm AddSemiconjBy.neg_neg_symm

end DivisionMonoid

section Group
variable [Group G] {a x y : G}

@[to_additive (attr := simp)] lemma inv_symm_left_iff : SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y := by
  simp_rw [SemiconjBy, eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]
#align semiconj_by.inv_symm_left_iff SemiconjBy.inv_symm_left_iff
#align add_semiconj_by.neg_symm_left_iff AddSemiconjBy.neg_symm_left_iff

@[to_additive] alias ⟨_, inv_symm_left⟩ := inv_symm_left_iff
#align semiconj_by.inv_symm_left SemiconjBy.inv_symm_left
#align add_semiconj_by.neg_symm_left AddSemiconjBy.neg_symm_left

@[to_additive (attr := simp)] lemma inv_right_iff : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y := by
  rw [← inv_symm_left_iff, inv_inv_symm_iff]
#align add_semiconj_by.neg_right_iff AddSemiconjBy.neg_right_iff

@[to_additive] alias ⟨_, inv_right⟩ := inv_right_iff
#align semiconj_by.inv_right SemiconjBy.inv_right
#align add_semiconj_by.neg_right AddSemiconjBy.neg_right

@[to_additive (attr := simp)] lemma zpow_right (h : SemiconjBy a x y) :
    ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ)    => by simp [zpow_natCast, h.pow_right n]
  | .negSucc n => by
    simp only [zpow_negSucc, inv_right_iff]
    apply pow_right h
#align semiconj_by.zpow_right SemiconjBy.zpow_right
#align add_semiconj_by.zsmul_right AddSemiconjBy.zsmul_right

end Group
end SemiconjBy
