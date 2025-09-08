import Mathlib

open Real

example {x : ℝ} (h : ∀ k : ℤ, x ≠ (2 * k + 1) * π / 2) :
    sin x = (2 * tan (x / 2)) / (1 + tan (x / 2) ^ 2) := by
  --apply?
  sorry
