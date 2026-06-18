module
import Mathlib

/-! Test that `simp` can prove some lemmas about derivatives. -/

open Real

example (x : ℝ) : deriv (fun x => cos x + 2 * sin x) x = -sin x + 2 * cos x := by
  simp

example (x : ℝ) :
    deriv (fun x ↦ cos (sin x) * exp x) x = (cos (sin x) - sin (sin x) * cos x) * exp x := by
  simp; ring

example (x : ℝ) : deriv (HAdd.hAdd 3) x = 1 := by
  simp

example (x : ℝ) : deriv (HSub.hSub 3) x = -1 := by
  simp

example (x : ℝ) : deriv (HMul.hMul 3) x = 3 := by
  simp

example (x : ℝ) : deriv (HDiv.hDiv 3) x = -3 / x ^ 2 := by
  simp

example (x : ℝ) : deriv (HPow.hPow 3) x = log 3 * 3 ^ x := by
  simp

example {x : ℝ} : deriv (fun x => (3 + x) * 2) x = 2 := by
  simp

example {x : ℝ} : deriv (fun x => (3 - x) * 2) x = -2 := by
  simp

example {x : ℝ} : deriv (fun x => (3 * x) * 2) x = 6 := by
  simp
  ring

example {x : ℝ} : deriv (fun x => (3 / x) * 2) x = -6 / x ^ 2 := by
  simp
  ring

example {x : ℝ} : deriv (fun x => (3 ^ x : ℝ) * 2) x = 2 * Real.log 3 * 3 ^ x := by
  simp
  ring

/- for more complicated examples (with more nested functions) you need to increase the
`maxDischargeDepth`. -/

example (x : ℝ) :
    deriv (fun x ↦ sin (sin (sin x)) + sin x) x =
    cos (sin (sin x)) * (cos (sin x) * cos x) + cos x := by
  simp (maxDischargeDepth := 3)

example (x : ℝ) :
    deriv (fun x ↦ sin (sin (sin x)) ^ 10 + sin x) x =
    10 * sin (sin (sin x)) ^ 9 * (cos (sin (sin x)) * (cos (sin x) * cos x)) + cos x := by
  simp (maxDischargeDepth := 4)
