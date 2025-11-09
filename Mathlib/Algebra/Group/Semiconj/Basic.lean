/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Algebra.Group.Basic

/-!
# Lemmas about semiconjugate elements of a group

-/

assert_not_exists MonoidWithZero DenselyOrdered

namespace SemiconjBy
variable {G : Type*}

section DivisionMonoid
variable [DivisionMonoid G] {a x y : G}

@[to_additive (attr := simp)]
theorem inv_inv_symm_iff : SemiconjBy a⁻¹ x⁻¹ y⁻¹ ↔ SemiconjBy a y x := by
  simp_rw [SemiconjBy, ← mul_inv_rev, inv_inj, eq_comm]

@[to_additive] alias ⟨_, inv_inv_symm⟩ := inv_inv_symm_iff

end DivisionMonoid

section Group
variable [Group G] {a x y : G}

@[to_additive (attr := simp)] lemma inv_symm_left_iff : SemiconjBy a⁻¹ y x ↔ SemiconjBy a x y := by
  simp_rw [SemiconjBy, eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul, eq_comm]

@[to_additive] alias ⟨_, inv_symm_left⟩ := inv_symm_left_iff

@[to_additive (attr := simp)] lemma inv_right_iff : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y := by
  rw [← inv_symm_left_iff, inv_inv_symm_iff]

@[to_additive] alias ⟨_, inv_right⟩ := inv_right_iff

@[to_additive (attr := simp)] lemma zpow_right (h : SemiconjBy a x y) :
    ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ) => by simp [zpow_natCast, h.pow_right n]
  | .negSucc n => by
    simp only [zpow_negSucc, inv_right_iff]
    apply pow_right h

variable (a) in
@[to_additive] lemma eq_one_iff (h : SemiconjBy a x y) : x = 1 ↔ y = 1 := by
  rw [← conj_eq_one_iff (a := a) (b := x), h.eq, mul_inv_cancel_right]

end Group
end SemiconjBy
