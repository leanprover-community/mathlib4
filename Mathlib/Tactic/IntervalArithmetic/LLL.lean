module

public import Mathlib.Tactic.IntervalArithmetic.RatReal

set_option linter.style.header false

/- # Interval Arithmetic Tactic (Prototype) -/

-- Proves goals like:

example : √(√ 3 - √ 2) ≤ 0.564 := by interval RatReal 10000

example (x : ℝ) (hx : 1 < x) : 0 < x ^ 3 + x - 1  := by interval RatReal 0

example (x : ℝ) (hx : 2 ≤ x) : Real.exp (- x ^ 2) ≤ 0.1 := by interval RatReal 100

example (x y : ℝ) (hx_lb : 0 ≤ x) (hx_ub : x ≤ √(√3 - √2)) (hy : 0.15 ≤ y) : x ^ 2 ≤ √y := by
  interval RatReal 1000

-- disclaimer: proofs of `pow`, `sqrt` are sorried (though `pow` was fully proved for an earlier
-- prototype)

/- # Description

Currently the tactic takes **hypotheses** and **goals** in the form of strict or nonstrict
inequalities (although other forms like interval containment can easily be supported).

Each hypotheses must contain exactly one free variable isolated on either side. The other side
and both sides of the goal are allowed to be any expression in the target type built up of
free variables and supported (extensible) operations.

-/

/- # Limitations

One major limitation for interval arithmetic methods is the so called *dependency* problem:

-/

-- This:
example (x : ℝ) (hx_lb : 0 ≤ x) (hx_ub : x ≤ 1) : x ≤ x := by interval RatReal 100
-- Is treated the same as this:
example (x y : ℝ) (hx_lb : 0 ≤ x) (hx_ub : 0 ≤ x) (hy_lb : 0 ≤ y) (hy_ub : 0 ≤ y) : x ≤ y := by
  sorry


/-
There are some solutions (not implimented):

1. Preprocessing: Can possibly be implimented with a simp set? Maybe some sort of normalization
  like `ring_nf`.

2. Interval Splitting: Split the interval of each variable into sufficiently small pieces and
prove each case seperately. I have not implimented this but built the current implimentation with
this in mind.

-/

-- Cannot handle:
example (x : ℝ) (hx_lb : 0 ≤ x) (hx_ub : x ≤ 2) : 0 ≤ x ^ 2 - x + 1  := by interval RatReal 100


-- But can handle:
example (x : ℝ) (hx_lb : 0 ≤ x) (hx_ub : x < 1) : 0 ≤ x ^ 2 - x + 1 := by interval RatReal 100
example (x : ℝ) (hx_lb : 1 ≤ x) (hx_ub : x ≤ 2) : 0 ≤ x ^ 2 - x + 1 := by interval RatReal 100

/-

3. More complicated stuff (Taylor series approximation). I want to look into this possible making
use of autodiff (`fun_prop`) once its in Mathlib.

-/

/- # Speed

Is speed an issue? Isn't rational arithmetic too slow? Yes but you can impliment Dyadic
interval arithmetic (and without writing meta code).
-/
