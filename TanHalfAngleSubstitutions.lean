import Mathlib

open Real

variable {x : ℝ}

example (h : ∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) :
    sin x = (2 * tan (x / 2)) / (1 + tan (x / 2) ^ 2) := by
  --apply?
  sorry

example : sin x = (2 * tan (x / 2)) / (1 + tan (x / 2) ^ 2) := by
  sorry

example (h : ∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) :
    cos x = (1 - tan (x / 2) ^ 2) / (1 + tan (x / 2) ^ 2) := by
  --apply?
  sorry

example : tan x = (2 * tan (x / 2)) / (1 - tan (x / 2) ^ 2) := by
  conv_lhs => rw [show x = 2 * (x / 2) by group]
  exact tan_two_mul
