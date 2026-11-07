/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Sqrt

namespace Inclusion.Tests

example : √2 ∈ Set.Icc 1 2 := by dyadic_interval

example : √(-1) = 0 := by dyadic_interval

example : √0 = 0 := by dyadic_interval

example : √1 = 1 := by dyadic_interval

example : √9 = 3 := by dyadic_interval

example : √(1 / 4 : ℚ) = 0.5 := by dyadic_interval [prec := 2]

example : √1e12 = 1e6 := by dyadic_interval

example : √(√16) = 2 := by dyadic_interval

example {x y : ℝ} (hx : x ∈ Set.Icc (-0.5) 1.5) (hy₀ : -2 ≤ y) (hy₁ : y ≤ -1) :
    √(x ^ 2 + y ^ 2) + (1 / 2 : ℚ) * x * y ∈ Set.Icc (-0.5) 3 := by
  dyadic_interval [prec := 1]

example : 1.4142 < √2 := by dyadic_interval [prec := 30]

example : √2 ∈ Set.Ioo 1.4142 1.4143 := by dyadic_interval [prec := 30]

example : √2 + √3 ∈ Set.Icc 3.14 3.15 := by dyadic_interval [prec := 20]

example : 2 - √2 ∈ Set.Icc 0.58 0.59 := by dyadic_interval [prec := 20]

example : √2 * √2 ∈ Set.Icc 1.99 2.01 := by dyadic_interval [prec := 20]

example {x : ℝ} : 0 ≤ √x := by dyadic_interval

example {x : ℝ} (hx : x ∈ Set.Icc 1 4) : √x ∈ Set.Icc 1 2 := by dyadic_interval

example {x : ℝ} (hx : x ∈ Set.Icc 0 1) : √x ≤ 1 := by dyadic_interval

example {x : ℝ} (hx : x ∈ Set.Icc 4 9) : 2 ≤ √x := by dyadic_interval

example {x : ℝ} (hx : x ∈ Set.Icc 1 2) : √(x ^ 2) ∈ Set.Icc 1 2 := by dyadic_interval

example {x : ℝ} (hx : x ∈ Set.Icc (-2) (-1)) : √(x ^ 2) ∈ Set.Icc 1 2 := by dyadic_interval

example :
    √2 ∈ Set.Ioo
      1.4142135623730950488016887242096980785696718753769
      1.4142135623730950488016887242096980785696718753770 := by
  dyadic_interval [prec := 165]

example : |√3 - (5170128475599457 / 2984975067132296 : ℚ)| < 1e-31 := by
  dyadic_interval [prec := 200]

example {x : ℝ} (hx : x ∈ Set.Icc 0 1) : √x - x ∈ Set.Icc (-0.05) 0.27 := by
  dyadic_interval [binSplit := 6, prec := 10]

example {x : ℝ} (hx : x ∈ Set.Icc 0 1) : √x * (1 - x) ∈ Set.Icc 0 0.4 := by
  dyadic_interval [binSplit := 6, prec := 20]

/-- error: The inclusion check failed:
The proposition is provably false -/
#guard_msgs in
set_option linter.unusedTactic false in
example (h : False) : √2 < 1.414 := by
  dyadic_interval? [prec := 7]
  exact h.elim
