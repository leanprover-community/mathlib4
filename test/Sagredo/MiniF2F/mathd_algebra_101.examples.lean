-- from miniF2F https://github.com/facebookresearch
import Mathlib.Tactic.GPT.Sagredo.Dialog
import Mathlib.Data.Real.Basic

open Real

-- On 2023-05-28, gets it cleanly first time:
theorem mathd_algebra_101
  (x : ℝ)
  (h₀ : x^2 - 5 * x - 4 ≤ 10) :
  x ≥ -2 ∧ x ≤ 7 := by
  have h₁ : x^2 - 5 * x - 14 ≤ 0 := by linarith
  by_cases x < -2
  focus
    have h₃ : (x - 7) * (x + 2) > 0 := by nlinarith
    exfalso
    linarith
  focus
    by_cases x > 7
    focus
      have h₅ : (x - 7) * (x + 2) > 0 := by nlinarith
      exfalso
      linarith
    focus
      apply And.intro
      linarith
      linarith

example (x : ℝ) (h₀ : x^2 - 5 * x - 4 ≤ 10) : x ≥ -2 ∧ x ≤ 7 := by
  have h₁ : x^2 - 5 * x - 4 - 10 ≤ 0 := by
    linarith
  have h₂ : (x + 2) * (x - 7) ≤ 0 := by
    change x^2 - 5 * x - 14 ≤ 0 at h₁
    exact h₁
  cases le_or_gt x (-2) with
  | inl h₃ =>
    apply And.intro
    { exact le_of_lt h₄ }
    { have h₅ : (x - 7) ≤ 0 := nonpos_of_mul_nonpos_right h₂ (le_of_lt (sub_neg_of_lt h₄))
      linarith }
  | inr h₄ =>
    cases le_or_gt x 7 with
    | inl h₆ =>
      apply And.intro
      { have h₈ : (x + 2) ≥ 0 := nonneg_of_mul_nonneg_left h₂ (le_of_lt h₄)
        linarith }
      { exact h₆ }
    | inr h₇ =>
      exfalso
      have h₉ : (x + 2) * (x - 7) > 0 := mul_pos (sub_pos.mpr (lt_trans h₄ (lt_of_lt_of_le (by norm_num) (le_of_lt h₇)))) (sub_pos.mpr h₇)
      exact lt_irrefl 0 (lt_of_le_of_lt h₂ (by linarith))

example (x : ℝ) (h₀ : x^2 - 5 * x - 4 ≤ 10) : x ≥ -2 ∧ x ≤ 7 := by
  have h₁ : x^2 ≤ 5 * x + 14 := by linarith
  apply And.intro
  by_cases h₂ : x ≥ 0
  exact le_trans (le_of_lt (neg_lt_zero.mpr (by norm_num))) h₂
  contrapose! h₁ with h₃
  calc 5 * x + 14 < 5 * -2 + 14 : add_lt_add_of_lt_of_le (mul_lt_mul_of_neg_left h₃ (by linarith)) (le_refl _)
              ... < x^2 : by linarith
