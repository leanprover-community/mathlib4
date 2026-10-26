import Mathlib.Tactic.RealRootCount

open Polynomial

example : Fintype.card ((X ^ 5 - 4 * X + 2 : ℚ[X]).rootSet ℝ) = 3 := by real_root_count

example : Fintype.card ((X ^ 4 + X + 1 : ℚ[X]).rootSet ℝ) = 0 := by real_root_count

example : Fintype.card ((-2 * X ^ 3 + 8 * X : ℚ[X]).rootSet ℝ) = 3 := by real_root_count

example : Fintype.card ((6 * X - 3 : ℚ[X]).rootSet ℝ) = 1 := by real_root_count

example : Fintype.card ((X ^ 2 - C 3 : ℚ[X]).rootSet ℝ) = 2 := by real_root_count

example : Fintype.card ((X ^ 6 - 1000000 : ℚ[X]).rootSet ℝ) = 2 := by real_root_count

-- Repeated roots, rational coefficients, constants and other coefficient rings.
example : Fintype.card (((X - 1) ^ 2 * (X + 2) ^ 3 * (X ^ 2 + 1) : ℚ[X]).rootSet ℝ) = 2 := by
  real_root_count

example : Fintype.card ((X + C (1 / 2) : ℚ[X]).rootSet ℝ) = 1 := by real_root_count

example : Fintype.card ((2 : ℚ[X]).rootSet ℝ) = 0 := by real_root_count

example : Fintype.card ((X ^ 2 - 2 : ℤ[X]).rootSet ℝ) = 2 := by real_root_count

example : Fintype.card ((X ^ 2 - 2 : ℝ[X]).rootSet ℝ) = 2 := by real_root_count

-- The `norm_root_count` simproc.
example : Fintype.card ((X ^ 5 - 4 * X + 2 : ℚ[X]).rootSet ℝ) = 3 := by simp only [norm_root_count]

example : Fintype.card ((X ^ 2 - 2 : ℚ[X]).rootSet ℝ) + 1 = 3 := by simp only [norm_root_count]

/-- error: real_root_count: expected a nonzero polynomial -/
#guard_msgs in
example : Fintype.card ((0 : ℚ[X]).rootSet ℝ) = 0 := by real_root_count

/--
error: real_root_count: cannot read
  p
in a polynomial with rational coefficients
-/
#guard_msgs in
example (p : ℚ[X]) : Fintype.card (p.rootSet ℝ) = 1 := by real_root_count

/-- error: real_root_count: the polynomial has 2 distinct real roots, not 1 -/
#guard_msgs in
example : Fintype.card ((X ^ 2 - 1 : ℚ[X]).rootSet ℝ) = 1 := by real_root_count

/-- error: real_root_count: expected a goal `Fintype.card (f.rootSet ℝ) = n` -/
#guard_msgs in
example : True := by real_root_count
