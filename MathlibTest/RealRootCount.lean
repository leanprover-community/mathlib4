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

noncomputable def nestedPolynomial : ℚ[X] := testPolynomial * (X ^ 2 + 1)

example : Fintype.card (nestedPolynomial.rootSet ℝ) = 1 :=
  real_root_count nestedPolynomial

example : Fintype.card ((X ^ 2 - C 3 : ℚ[X]).rootSet ℝ) = 2 :=
  real_root_count (X ^ 2 - C 3 : ℚ[X])

example : Fintype.card ((X ^ 3 - 2 : ℚ[X]).rootSet ℝ) = 1 :=
  real_root_count (let p : ℚ[X] := X ^ 3; p - 2)

example : Fintype.card ((X ^ 6 - 1000000 : ℚ[X]).rootSet ℝ) = 2 :=
  real_root_count (X ^ 6 - 1000000 : ℚ[X])

/-- error: real_root_count: expected a squarefree polynomial -/
#guard_msgs in
example := real_root_count ((X - 1) ^ 2 : ℚ[X])

/-- error: real_root_count: expected a nonzero polynomial -/
#guard_msgs in
example := real_root_count (0 : ℚ[X])

/-- error: real_root_count: expected a polynomial of positive degree -/
#guard_msgs in
example := real_root_count (2 : ℚ[X])

/--
error: real_root_count: non-integer coefficient
  1 / 2
-/
#guard_msgs in
example := real_root_count (X + C (1 / 2) : ℚ[X])

/-- error: real_root_count: expected a closed polynomial -/
#guard_msgs in
example (p : ℚ[X]) := real_root_count p

-- A valid certificate must still prove the count requested by the caller.
example : True := by
  fail_if_success have : Fintype.card ((X ^ 2 - 1 : ℚ[X]).rootSet ℝ) = 1 :=
    real_root_count (X ^ 2 - 1 : ℚ[X])
  trivial

example : Fintype.card ((X ^ 5 - 4 * X + 2 : ℚ[X]).rootSet ℝ) = 3 := by
  real_root_count

example : Fintype.card (nestedPolynomial.rootSet ℝ) = 1 := by
  real_root_count

/-- error: real_root_count: expected a goal `Fintype.card (p.rootSet ℝ) = n` -/
#guard_msgs in
example : True := by real_root_count
