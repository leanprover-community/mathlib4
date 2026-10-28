/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Log

open Real

namespace Inclusion.Tests

example {x : ℝ} (hx : x ∈ Set.Icc 0.5 4) : log x ∈ Set.Icc (-0.693148) 1.38630 := by
  dyadic_interval [prec := 30]

example : log 0 = 0 := by
  dyadic_interval

example : log 1 = 0 := by
  dyadic_interval

example : log (-1) = 0 := by
  dyadic_interval

example :
  log 2 ∈ Set.Icc
    0.69314718055994530941723212145817656807550013436025
    0.69314718055994530941723212145817656807550013436026 := by
  dyadic_interval [prec := 170]

example :
    |log 2 - (1143 / 1649 : ℚ)| < 1e-6 := by
  dyadic_interval [prec := 100]

example :
    |log 2 - (48427462327 / 69866059742 : ℚ)| < 1e-22 := by
  dyadic_interval [prec := 200]

example :
    |log 3 - (5318521110702888 / 4841126542604705 : ℚ)| < 1e-31 := by
  dyadic_interval [prec := 200]

example :
    |log 10 - (227480160645689 / 98793378510888 : ℚ)| < 1e-30 := by
  dyadic_interval [prec := 200]

example {x : ℝ} (hx : x ∈ Set.Icc 0 1) :
    log (log (x ^ 2 + 1) + 2) ∈ Set.Icc 0.693 0.991 := by
  dyadic_interval [prec := 20]

example {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    x ^ 3 + log (x + 2) ∈ Set.Icc (-1) 2.1 := by
  dyadic_interval [prec := 20]

example {x y : ℝ} (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc 1 2) :
    x ^ 2 + y ^ 2 + log (x + y) ∈ Set.Icc 2.69 9.39 := by
  dyadic_interval [prec := 20]
