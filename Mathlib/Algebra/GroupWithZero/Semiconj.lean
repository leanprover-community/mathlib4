/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Group.Semiconj.Units
import Mathlib.Init.Classical

#align_import algebra.group_with_zero.semiconj from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Lemmas about semiconjugate elements in a `GroupWithZero`.

-/

assert_not_exists DenselyOrdered

variable {α M₀ G₀ M₀' G₀' F F' : Type*}

namespace SemiconjBy

@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : SemiconjBy a 0 0 := by
  simp only [SemiconjBy, mul_zero, zero_mul]
#align semiconj_by.zero_right SemiconjBy.zero_right

@[simp]
theorem zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjBy 0 x y := by
  simp only [SemiconjBy, mul_zero, zero_mul]
#align semiconj_by.zero_left SemiconjBy.zero_left

variable [GroupWithZero G₀] {a x y x' y' : G₀}

@[simp]
theorem inv_symm_left_iff₀ : SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x :=
  Classical.by_cases (fun ha : a = 0 => by simp only [ha, inv_zero, SemiconjBy.zero_left]) fun ha =>
    @units_inv_symm_left_iff _ _ (Units.mk0 a ha) _ _
#align semiconj_by.inv_symm_left_iff₀ SemiconjBy.inv_symm_left_iff₀

theorem inv_symm_left₀ (h : SemiconjBy a x y) : SemiconjBy a⁻¹ y x :=
  SemiconjBy.inv_symm_left_iff₀.2 h
#align semiconj_by.inv_symm_left₀ SemiconjBy.inv_symm_left₀

theorem inv_right₀ (h : SemiconjBy a x y) : SemiconjBy a x⁻¹ y⁻¹ := by
  by_cases ha : a = 0
  · simp only [ha, zero_left]
  by_cases hx : x = 0
  · subst x
    simp only [SemiconjBy, mul_zero, @eq_comm _ _ (y * a), mul_eq_zero] at h
    simp [h.resolve_right ha]
  · have := mul_ne_zero ha hx
    rw [h.eq, mul_ne_zero_iff] at this
    exact @units_inv_right _ _ _ (Units.mk0 x hx) (Units.mk0 y this.1) h
#align semiconj_by.inv_right₀ SemiconjBy.inv_right₀

@[simp]
theorem inv_right_iff₀ : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y :=
  ⟨fun h => inv_inv x ▸ inv_inv y ▸ h.inv_right₀, inv_right₀⟩
#align semiconj_by.inv_right_iff₀ SemiconjBy.inv_right_iff₀

theorem div_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x / x') (y / y') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h.mul_right h'.inv_right₀
#align semiconj_by.div_right SemiconjBy.div_right

lemma zpow_right₀ {a x y : G₀} (h : SemiconjBy a x y) : ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ) => by simp [h.pow_right n]
  | .negSucc n => by simp only [zpow_negSucc, (h.pow_right (n + 1)).inv_right₀]
#align semiconj_by.zpow_right₀ SemiconjBy.zpow_right₀

end SemiconjBy

namespace Commute
variable [GroupWithZero G₀] {a b : G₀}

lemma zpow_right₀ (h : Commute a b) : ∀ m : ℤ, Commute a (b ^ m) := SemiconjBy.zpow_right₀ h
#align commute.zpow_right₀ Commute.zpow_right₀

lemma zpow_left₀ (h : Commute a b) (m : ℤ) : Commute (a ^ m) b := (h.symm.zpow_right₀ m).symm
#align commute.zpow_left₀ Commute.zpow_left₀

lemma zpow_zpow₀ (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left₀ m).zpow_right₀ n
#align commute.zpow_zpow₀ Commute.zpow_zpow₀

lemma zpow_self₀ (a : G₀) (n : ℤ) : Commute (a ^ n) a := (Commute.refl a).zpow_left₀ n
#align commute.zpow_self₀ Commute.zpow_self₀

lemma self_zpow₀ (a : G₀) (n : ℤ) : Commute a (a ^ n) := (Commute.refl a).zpow_right₀ n
#align commute.self_zpow₀ Commute.self_zpow₀

lemma zpow_zpow_self₀ (a : G₀) (m n : ℤ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).zpow_zpow₀ m n
#align commute.zpow_zpow_self₀ Commute.zpow_zpow_self₀

end Commute
