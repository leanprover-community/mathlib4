/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

open Inclusion

namespace Inclusion.Tests

section Interval

private def closed (lb ub : Dyadic) : Interval Dyadic := Interval.Icc lb ub

private def atLeast (lb : Dyadic) : Interval Dyadic := Interval.Ici lb

private def atMost (ub : Dyadic) : Interval Dyadic := Interval.Iic ub

-- The nine possible pairs of interval signs use their sharp endpoint formulas.
example : (closed 1 2).mul (closed 3 4) = closed 3 8 := by rfl

example : (closed 1 2).mul (closed (-3) 4) = closed (-6) 8 := by rfl

example : (closed 1 2).mul (closed (-4) (-3)) = closed (-8) (-3) := by rfl

example : (closed (-2) 3).mul (closed 4 5) = closed (-10) 15 := by rfl

example : (closed (-2) 3).mul (closed (-5) 7) = closed (-15) 21 := by rfl

example : (closed (-2) 3).mul (closed (-5) (-4)) = closed (-15) 10 := by rfl

example : (closed (-3) (-2)).mul (closed 4 5) = closed (-15) (-8) := by rfl

example : (closed (-3) (-2)).mul (closed (-4) 5) = closed (-15) 12 := by rfl

example : (closed (-3) (-2)).mul (closed (-5) (-4)) = closed 8 15 := by rfl

-- Infinite endpoints propagate according to sign, while zero times an unbounded interval is zero.
example : (atLeast 3).mul (atLeast 2) = atLeast 6 := by rfl

example : (atMost (-3)).mul (atMost (-2)) = atLeast 6 := by rfl

example : (Interval.singleton (0 : Dyadic)).mul (Interval.univ Dyadic) =
    Interval.singleton 0 := by rfl

example : (atLeast 0).mul (atMost 0) = atMost 0 := by rfl

example : (atLeast 2).mul (closed (-3) 4) =
    Interval.univ Dyadic := by rfl

end Interval

section Tactic

example {x y : ℝ} (hx : x ∈ Set.Icc 1 2) (hy : y ∈ Set.Icc 3 4) :
    x * y ∈ Set.Icc 3 8 := by dyadic_interval

example {x y : ℝ} (hx : x ∈ Set.Icc (-2) 3) (hy : y ∈ Set.Icc (-5) 7) :
    x * y ∈ Set.Icc (-15) 21 := by dyadic_interval

example {x y : ℝ} (hx : 3 ≤ x) (hy : 2 ≤ y) : 6 ≤ x * y := by dyadic_interval

example {x y : ℝ} (hx : x ≤ -3) (hy : y ≤ -2) : 6 ≤ x * y := by dyadic_interval

example {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 0) : x * y ≤ 0 := by dyadic_interval

example {x y : ℝ} (hx : x = 0) : x * y = 0 := by dyadic_interval

example {x y : ℝ} (hx : x ∈ Set.Icc (-1.25) 2.5) (hy : y ∈ Set.Icc 3 4) :
    x * y ∈ Set.Icc (-5) 10 := by dyadic_interval [prec := 2]

example {x y z : ℝ} (hx : x ∈ Set.Icc (-2) 3) (hy : y ∈ Set.Icc 1 4)
    (hz : z ∈ Set.Icc (-1) 2) : x * y + z ∈ Set.Icc (-9) 14 := by dyadic_interval

example {x y : ℝ} (hx : x ∈ Set.Icc ((1 / 3 : ℚ) : ℝ) ((2 / 3 : ℚ) : ℝ))
    (hy : y ∈ Set.Icc 3 6) : x * y ∈ Set.Icc 0.9 4.1 := by
  dyadic_interval [prec := 12]

example {x : ℝ} (hx : x ∈ Set.Icc (-2) 2) : 0 ≤ x * x := by
  dyadic_interval [binSplit := 1]

end Tactic

section Kernel

example {a b c d e f : ℝ} (ha : a ∈ Set.Icc (-2) 3) (hb : b ∈ Set.Icc (-4) 5)
    (hc : c ∈ Set.Icc 1 2) (hd : d ∈ Set.Icc (-3) (-1)) (he : e ∈ Set.Icc 2 4)
    (hf : f ∈ Set.Icc (-1) 1) : a * b + c * d + e * f ∈ Set.Icc (-27) 25 := by
  dyadic_interval +kernel

end Kernel

end Inclusion.Tests
