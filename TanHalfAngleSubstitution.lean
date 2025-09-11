import Mathlib

open Complex
open scoped Real

variable (x : ℂ)

-- tangent half-angle substitution formulas

lemma one_add_tan_sq_mul_cos_sq_eq_one {x : ℂ} (h : cos x ≠ 0) : (1 + tan x ^ 2) * cos x ^ 2 = 1 := by
  conv_rhs => rw [← sin_sq_add_cos_sq x, ← tan_mul_cos h]
  ring

lemma div_one_add_tan_sq_eq_cos_sq {x y : ℂ} (h : cos x ≠ 0) : y / (1 + tan x ^ 2) = y * cos x ^ 2 := by
  rw [← mul_div_mul_right _ _ (pow_ne_zero 2 h), one_add_tan_sq_mul_cos_sq_eq_one h]
  simp

/-- `tan x` takes the junk value `0` when `cos x = 0` -/
lemma tan_eq_zero_of_cos_eq_zero (h : cos x = 0) : tan x = 0 := by
  obtain ⟨k, hxk⟩ := cos_eq_zero_iff.mp h
  exact tan_eq_zero_iff.mpr ⟨2 * k + 1, by simp [hxk]⟩

/-- `tan (x / 2)` takes the junk value `0` when `sin x = 0` so this always holds. -/
theorem sin_eq_two_mul_tan_half_div_one_add_tan_half_sq :
    sin x = (2 * tan (x / 2)) / (1 + tan (x / 2) ^ 2) := by
  conv_lhs => rw [show x = 2 * (x / 2) by group, sin_two_mul]
  by_cases h : cos (x / 2) = 0
  · simp [h, tan_eq_zero_of_cos_eq_zero]
  . rw [div_one_add_tan_sq_eq_cos_sq h, ← tan_mul_cos h]
    group

theorem cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq'' (h : cos (x / 2) ≠ 0) :
    cos x = (1 - tan (x / 2) ^ 2) / (1 + tan (x / 2) ^ 2) := by
  conv_lhs => rw [show x = 2 * (x / 2) by group, cos_two_mul']
  rw [div_one_add_tan_sq_eq_cos_sq h, ← tan_mul_cos h]
  ring

theorem cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq' (h : ∀ k : ℤ, x ≠ (2 * k + 1) * π) :
    cos x = (1 - tan (x / 2) ^ 2) / (1 + tan (x / 2) ^ 2) :=
  cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq'' x (by grind [cos_ne_zero_iff])

theorem cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq (h : cos x ≠ -1) :
    cos x = (1 - tan (x / 2) ^ 2) / (1 + tan (x / 2) ^ 2) := by
  exact cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq' x (by grind [cos_eq_neg_one_iff])

theorem tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq :
    tan x = (2 * tan (x / 2)) / (1 - tan (x / 2) ^ 2) := by
  conv_lhs => rw [show x = 2 * (x / 2) by group, tan_two_mul]
