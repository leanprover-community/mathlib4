/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Group.Semiconj.Units

/-!
# Lemmas about semiconjugate elements in a `GroupWithZero`.

-/

assert_not_exists DenselyOrdered Ring

variable {G₀ : Type*}

namespace SemiconjBy

@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : SemiconjBy a 0 0 := by
  simp only [SemiconjBy, mul_zero, zero_mul]

@[simp]
theorem zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjBy 0 x y := by
  simp only [SemiconjBy, mul_zero, zero_mul]

variable [GroupWithZero G₀] {a x y x' y' : G₀}

@[simp]
theorem inv_symm_left_iff₀ : SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x :=
  Classical.by_cases (fun ha : a = 0 => by simp only [ha, inv_zero, SemiconjBy.zero_left]) fun ha =>
    @units_inv_symm_left_iff _ _ (Units.mk0 a ha) _ _

theorem inv_symm_left₀ (h : SemiconjBy a x y) : SemiconjBy a⁻¹ y x :=
  SemiconjBy.inv_symm_left_iff₀.2 h

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

@[simp]
theorem inv_right_iff₀ : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y :=
  ⟨fun h => inv_inv x ▸ inv_inv y ▸ h.inv_right₀, inv_right₀⟩

theorem div_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x / x') (y / y') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h.mul_right h'.inv_right₀

lemma zpow_right₀ {a x y : G₀} (h : SemiconjBy a x y) : ∀ m : ℤ, SemiconjBy a (x ^ m) (y ^ m)
  | (n : ℕ) => by simp [h.pow_right n]
  | .negSucc n => by simp only [zpow_negSucc, (h.pow_right (n + 1)).inv_right₀]

end SemiconjBy

namespace Commute
variable [GroupWithZero G₀] {a b : G₀}

lemma zpow_right₀ (h : Commute a b) : ∀ m : ℤ, Commute a (b ^ m) := SemiconjBy.zpow_right₀ h

lemma zpow_left₀ (h : Commute a b) (m : ℤ) : Commute (a ^ m) b := (h.symm.zpow_right₀ m).symm

lemma zpow_zpow₀ (h : Commute a b) (m n : ℤ) : Commute (a ^ m) (b ^ n) :=
  (h.zpow_left₀ m).zpow_right₀ n

lemma zpow_self₀ (a : G₀) (n : ℤ) : Commute (a ^ n) a := (Commute.refl a).zpow_left₀ n

lemma self_zpow₀ (a : G₀) (n : ℤ) : Commute a (a ^ n) := (Commute.refl a).zpow_right₀ n

lemma zpow_zpow_self₀ (a : G₀) (m n : ℤ) : Commute (a ^ m) (a ^ n) :=
  (Commute.refl a).zpow_zpow₀ m n

end Commute
