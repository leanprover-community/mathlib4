-- from miniF2F https://github.com/facebookresearch
import Mathlib.Tactic.GPT.Sagredo.Widget
import Mathlib.Data.Real.Basic

open Real

theorem quadratic_inequality (x : ℝ) (h₀ : x ^ 2 - 5 * x - 4 ≤ 10) : x ≥ -2 ∧ x ≤ 7 := by
  have h₁ : x ^ 2 - 5 * x - 14 ≤ 0 := by linarith
  have h₂ : (x - 7) * (x + 2) ≤ 0 := by
    have h₃ : x ^ 2 - 5 * x - 14 = (x - 7) * (x + 2) := by ring
    rw [h₃] at h₁
    exact h₁
  cases lt_or_ge x (-2) with
  | inl h₃ =>
    have h₅ : (x - 7) * (x + 2) > 0 := by nlinarith
    exfalso
    linarith
  | inr h₄ =>
    apply And.intro h₄
    by_contra h
    push_neg at h
    have h₅ : (x - 7) * (x + 2) > 0 := by
      apply mul_pos
      exact sub_pos_of_lt h
      linarith
    linarith
