import Mathlib

open Real

variable (x : ℝ)

-- tangent half-angle substitution formulas

lemma one_add_tan_sq_mul_cos_sq_eq_one (h : cos x ≠ 0) : (1 + tan x ^ 2) * cos x ^ 2 = 1 := by
  conv_rhs => rw [← sin_sq_add_cos_sq x, ← tan_mul_cos h]
  ring

/-- `tan x` takes the junk value `0` when `cos x = 0` -/
lemma tan_eq_zero_of_cos_eq_zero (h : cos x = 0) : tan x = 0 := by
  sorry

/-- `tan (x / 2)` takes the junk value `0` when `sin x = 0` so this always holds. -/
theorem sin_eq_two_mul_tan_half_div_one_add_tan_half_sq :
    sin x = (2 * tan (x / 2)) / (1 + tan (x / 2) ^ 2) := by
  conv_lhs => rw [show x = 2 * (x / 2) by group, sin_two_mul]
  by_cases h : cos (x / 2) = 0
  · simp [h]
    have : tan (x / 2) = 0 := by
      rw [cos_eq_zero_iff] at h
      obtain ⟨k, hxk⟩ := h
      apply tan_eq_zero_iff.mpr
      use 2 * k + 1
      push_cast
      exact hxk.symm
    simp [this]
  . conv_rhs => rw [← mul_div_mul_right _ _ (pow_ne_zero 2 h), one_add_tan_sq_mul_cos_sq_eq_one (x / 2) h]
    rw [← tan_mul_cos h]
    group

theorem cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq (h : cos x ≠ -1) :
    cos x = (1 - tan (x / 2) ^ 2) / (1 + tan (x / 2) ^ 2) := by
  --apply?
  sorry

theorem cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq' (h : ∀ k : ℤ, x ≠ (2 * k + 1) * π) :
    cos x = (1 - tan (x / 2) ^ 2) / (1 + tan (x / 2) ^ 2) := by
  sorry

theorem tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq :
    tan x = (2 * tan (x / 2)) / (1 - tan (x / 2) ^ 2) := by
  conv_lhs => rw [show x = 2 * (x / 2) by group, tan_two_mul]
