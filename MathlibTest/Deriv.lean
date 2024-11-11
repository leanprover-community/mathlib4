import Mathlib

/-! Test that `simp` can prove some lemmas about derivatives. -/

open Real

example (x : ℝ) : deriv (λ x => cos x + 2 * sin x) x = -sin x + 2 * cos x := by
  simp

example (x : ℝ) :
    deriv (fun x ↦ cos (sin x) * exp x) x = (cos (sin x) - sin (sin x) * cos x) * exp x := by
  simp; ring
