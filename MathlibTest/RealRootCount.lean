import Mathlib.Tactic.RealRootCount

open Polynomial

example : Fintype.card ((X ^ 5 - 4 * X + 2 : ℚ[X]).rootSet ℝ) = 3 :=
  real_root_count (X ^ 5 - 4 * X + 2 : ℚ[X])

example : Fintype.card ((X ^ 4 + X + 1 : ℚ[X]).rootSet ℝ) = 0 :=
  real_root_count (X ^ 4 + X + 1 : ℚ[X])

example : Fintype.card ((-2 * X ^ 3 + 8 * X : ℚ[X]).rootSet ℝ) = 3 :=
  real_root_count (-2 * X ^ 3 + 8 * X : ℚ[X])

example : Fintype.card ((6 * X - 3 : ℚ[X]).rootSet ℝ) = 1 :=
  real_root_count (6 * X - 3 : ℚ[X])

noncomputable def testPolynomial : ℚ[X] := X ^ 3 - 2

example : Fintype.card (testPolynomial.rootSet ℝ) = 1 :=
  real_root_count testPolynomial

example : True := by
  fail_if_success have : Fintype.card ((X ^ 2 - 1 : ℚ[X]).rootSet ℝ) = 1 :=
    real_root_count (X ^ 2 - 1 : ℚ[X])
  fail_if_success have := real_root_count ((X - 1) ^ 2 : ℚ[X])
  fail_if_success have := real_root_count (0 : ℚ[X])
  fail_if_success have := real_root_count (2 : ℚ[X])
  fail_if_success have := real_root_count (X + C (1 / 2) : ℚ[X])
  trivial
