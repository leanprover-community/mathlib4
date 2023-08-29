/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Group.Semiconj
import Mathlib.Init.Classical

#align_import algebra.group_with_zero.semiconj from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Lemmas about semiconjugate elements in a `GroupWithZero`.

-/


variable {α M₀ G₀ M₀' G₀' F F' : Type*}

namespace SemiconjBy

@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : SemiconjBy a 0 0 := by
  simp only [SemiconjBy, mul_zero, zero_mul]
  -- 🎉 no goals
#align semiconj_by.zero_right SemiconjBy.zero_right

@[simp]
theorem zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjBy 0 x y := by
  simp only [SemiconjBy, mul_zero, zero_mul]
  -- 🎉 no goals
#align semiconj_by.zero_left SemiconjBy.zero_left

variable [GroupWithZero G₀] {a x y x' y' : G₀}

@[simp]
theorem inv_symm_left_iff₀ : SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x :=
  Classical.by_cases (fun ha : a = 0 => by simp only [ha, inv_zero, SemiconjBy.zero_left]) fun ha =>
                                           -- 🎉 no goals
    @units_inv_symm_left_iff _ _ (Units.mk0 a ha) _ _
#align semiconj_by.inv_symm_left_iff₀ SemiconjBy.inv_symm_left_iff₀

theorem inv_symm_left₀ (h : SemiconjBy a x y) : SemiconjBy a⁻¹ y x :=
  SemiconjBy.inv_symm_left_iff₀.2 h
#align semiconj_by.inv_symm_left₀ SemiconjBy.inv_symm_left₀

theorem inv_right₀ (h : SemiconjBy a x y) : SemiconjBy a x⁻¹ y⁻¹ := by
  by_cases ha : a = 0
  -- ⊢ SemiconjBy a x⁻¹ y⁻¹
  · simp only [ha, zero_left]
    -- 🎉 no goals
  by_cases hx : x = 0
  -- ⊢ SemiconjBy a x⁻¹ y⁻¹
  · subst x
    -- ⊢ SemiconjBy a 0⁻¹ y⁻¹
    simp only [SemiconjBy, mul_zero, @eq_comm _ _ (y * a), mul_eq_zero] at h
    -- ⊢ SemiconjBy a 0⁻¹ y⁻¹
    simp [h.resolve_right ha]
    -- 🎉 no goals
  · have := mul_ne_zero ha hx
    -- ⊢ SemiconjBy a x⁻¹ y⁻¹
    rw [h.eq, mul_ne_zero_iff] at this
    -- ⊢ SemiconjBy a x⁻¹ y⁻¹
    exact @units_inv_right _ _ _ (Units.mk0 x hx) (Units.mk0 y this.1) h
    -- 🎉 no goals
#align semiconj_by.inv_right₀ SemiconjBy.inv_right₀

@[simp]
theorem inv_right_iff₀ : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y :=
  ⟨fun h => inv_inv x ▸ inv_inv y ▸ h.inv_right₀, inv_right₀⟩
#align semiconj_by.inv_right_iff₀ SemiconjBy.inv_right_iff₀

theorem div_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x / x') (y / y') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  -- ⊢ SemiconjBy a (x * x'⁻¹) (y * y'⁻¹)
  exact h.mul_right h'.inv_right₀
  -- 🎉 no goals
#align semiconj_by.div_right SemiconjBy.div_right

end SemiconjBy
