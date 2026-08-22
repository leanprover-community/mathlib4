module

import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.IntervalArithmetic.Interval
public meta import Mathlib.Tactic.IntervalArithmetic.DyadicReal
public meta import Mathlib.Tactic.IntervalArithmetic.ExactRatReal

set_option linter.style.header false

set_option trace.profiler true

example : 3.1415926535 ≤ Real.pi := by
  dyadic_interval [approx := 50]

example : 3.1415926535 + 3.1415926535 ≤ Real.pi + Real.pi := by
  dyadic_interval [approx := 50]

example : 3.1415926535 + 3.1415926535 + 3.1415926535 ≤ Real.pi + Real.pi + Real.pi  := by
  dyadic_interval [approx := 50]

-- 0.106895
example (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    Real.exp x ≤ 2.7182818284591 := by
  dyadic_interval [approx := 53]

-- 0.098868
example (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    Real.exp x + Real.exp x ≤ 5.4365636569182 := by
  dyadic_interval [approx := 53]

-- 0.096682
example (x y : ℝ) (hx : x ∈ Set.Icc 0 1) (hx : y ∈ Set.Icc 0 1) :
    Real.exp x + Real.exp y  ≤ 5.4365636569182 := by
  dyadic_interval [approx := 53]

-- 0.110107
example (x y : ℝ) (hx : x ∈ Set.Icc 0 2) (hx : y ∈ Set.Icc 0 2) :
    Real.exp x + Real.exp y ≤ 14.7781121978614 := by
  dyadic_interval [approx := 55]

-- 0.158724
example (x y : ℝ) (hx : x ∈ Set.Icc 0 1) (hx : y ∈ Set.Icc 0 2) :
    Real.exp x + Real.exp y ≤ 10.1073379273898 := by
  dyadic_interval [approx := 55]

example (x y : ℝ) (hx : x ∈ Set.Icc 0 1) (hx : y ∈ Set.Icc 0 2) :
    -1 ≤ Real.exp x + Real.exp y := by
  dyadic_interval [approx := 550]
