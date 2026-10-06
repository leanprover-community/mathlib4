module
import Mathlib
public meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

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

example : (2 : ℝ) + 1 < 4 := by dyadic_interval [prec := 4]
example : (2 : ℝ) * 3 ≤ 7 := by dyadic_interval
theorem a : (2 : ℝ) ≠ 3 := by dyadic_interval
#print a

example (x : ℝ)
    (hx : x ∈ (Inclusion.Interval.Icc (0 : Dyadic) (1 : Dyadic) : Inclusion.Interval Dyadic)) :
    x + 1 < 3 := by dyadic_interval [prec := 10]

example (x : ℝ)
    (hx : x ∈ (Inclusion.Interval.Icc (0 : Dyadic) (1 : Dyadic) : Inclusion.Interval Dyadic)) :
    0 ≤ x * x := by dyadic_interval [prec := 10]


example (x y : ℝ)
    (hx : x ∈ (Inclusion.Interval.Icc (0 : Dyadic) (1 : Dyadic) : Inclusion.Interval Dyadic))
    (hy : y ∈ (Inclusion.Interval.Icc (0 : Dyadic) (1 : Dyadic) : Inclusion.Interval Dyadic)) :
    x + y < 3 := by dyadic_interval [prec := 10]


example (x : ℝ)
    (hx : x ∈ (Inclusion.Interval.Icc (0 : Dyadic) (1 : Dyadic) : Inclusion.Interval Dyadic)) :
    x ∈ Set.Icc (0 : ℝ) 2 := by dyadic_interval [prec := 10]


example : ((1 / 3 : ℚ) : ℝ) < 1 := by dyadic_interval [prec := 10]

example : (2 : ℝ) + 1 < 4 := by dyadic_interval +kernel [prec := 4]
#version
