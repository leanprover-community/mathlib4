module

import Mathlib.Tactic.NormRealRootCount

open Polynomial

example : Fintype.card ((X ^ 5 - 4 * X + 2 : ℚ[X]).rootSet ℝ) = 3 := by eval_real_root_count

example : Fintype.card ((X ^ 4 + X + 1 : ℚ[X]).rootSet ℝ) = 0 := by eval_real_root_count

example : Fintype.card ((-2 * X ^ 3 + 8 * X : ℚ[X]).rootSet ℝ) = 3 := by eval_real_root_count

example : Fintype.card ((6 * X - 3 : ℚ[X]).rootSet ℝ) = 1 := by eval_real_root_count

example : Fintype.card ((X ^ 2 - C 3 : ℚ[X]).rootSet ℝ) = 2 := by eval_real_root_count

example : Fintype.card ((X ^ 6 - 1000000 : ℚ[X]).rootSet ℝ) = 2 := by eval_real_root_count

example : Fintype.card (((X - 1) ^ 2 * (X + 2) ^ 3 * (X ^ 2 + 1) : ℚ[X]).rootSet ℝ) = 2 := by
  eval_real_root_count

example : Fintype.card ((X + C (1 / 2) : ℚ[X]).rootSet ℝ) = 1 := by eval_real_root_count

example : Fintype.card ((C (1 / 3) * X ^ 2 - C (1 / 2) * X - C (5 / 7) : ℚ[X]).rootSet ℝ) = 2 := by
  eval_real_root_count

example : Fintype.card ((2 : ℚ[X]).rootSet ℝ) = 0 := by eval_real_root_count

example : Fintype.card ((X ^ 2 - 2 : ℤ[X]).rootSet ℝ) = 2 := by eval_real_root_count

example : Fintype.card ((-2 * X ^ 2 + 4 : ℤ[X]).rootSet ℝ) = 2 := by eval_real_root_count

example : Fintype.card ((X ^ 2 - 2 : ℝ[X]).rootSet ℝ) = 2 := by eval_real_root_count

example : Fintype.card ((X ^ 2 - C (1 / 2) : ℝ[X]).rootSet ℝ) = 2 := by eval_real_root_count

example : Fintype.card ((X : ℚ[X]).rootSet ℝ) = 1 := by eval_real_root_count

example {R : Type*} [CommRing R] [Algebra R ℝ] :
    Fintype.card ((X ^ 2 - 2 : R[X]).rootSet ℝ) = 2 := by
  eval_real_root_count

example {K : Type*} [Field K] [CharZero K] [Algebra K ℝ] :
    Fintype.card ((X ^ 2 - C (1 / 2) * X - C (3 / 4 + 1) : K[X]).rootSet ℝ) = 2 := by
  eval_real_root_count

-- Lehmer's polynomial.
example : Fintype.card ((X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 :
    ℤ[X]).rootSet ℝ) = 2 := by
  eval_real_root_count

-- The cyclotomic polynomial `Φ₁₀₅`.
example : Fintype.card ((X ^ 48 + X ^ 47 + X ^ 46 - X ^ 43 - X ^ 42 - 2 * X ^ 41 - X ^ 40 - X ^ 39 +
    X ^ 36 + X ^ 35 + X ^ 34 + X ^ 33 + X ^ 32 + X ^ 31 - X ^ 28 - X ^ 26 - X ^ 24 - X ^ 22 -
    X ^ 20 + X ^ 17 + X ^ 16 + X ^ 15 + X ^ 14 + X ^ 13 + X ^ 12 - X ^ 9 - X ^ 8 - 2 * X ^ 7 -
    X ^ 6 - X ^ 5 + X ^ 2 + X + 1 : ℤ[X]).rootSet ℝ) = 0 := by
  eval_real_root_count

-- Klein's icosahedral equation `H ^ 3 = 1728 * Z * f ^ 5` at `Z = 2`, of degree 60.
example : Fintype.card (((-(X ^ 20 + 1) + 228 * (X ^ 15 - X ^ 5) - 494 * X ^ 10) ^ 3 -
    1728 * 2 * (X * (X ^ 10 + 11 * X ^ 5 - 1)) ^ 5 : ℤ[X]).rootSet ℝ) = 4 := by
  eval_real_root_count

example : Fintype.card ((X ^ 2 - 2 : ℚ[X]).rootSet ℝ) + 1 = 3 := by
  simp only [norm_real_root_count]

example : Fintype.card ((X ^ 2 - 2 : ℚ[X]).rootSet ℝ) + 1 = 3 := by eval_real_root_count

example : Fintype.card ((X ^ 5 - 4 * X + 2 : ℚ[X]).rootSet ℝ) ≤ 4 := by eval_real_root_count

/--
error: `eval_real_root_count` made no progress.
Additional information may be available using `set_option trace.Tactic.evalRealRootCount true`.
-/
#guard_msgs in
example : Fintype.card ((0 : ℚ[X]).rootSet ℝ) = 0 := by eval_real_root_count

/--
error: `eval_real_root_count` made no progress.
Additional information may be available using `set_option trace.Tactic.evalRealRootCount true`.
---
trace: [Tactic.evalRealRootCount] expected a nonzero polynomial
-/
#guard_msgs in
set_option trace.Tactic.evalRealRootCount true in
example : Fintype.card ((0 : ℚ[X]).rootSet ℝ) = 0 := by eval_real_root_count

/--
error: `eval_real_root_count` made no progress.
Additional information may be available using `set_option trace.Tactic.evalRealRootCount true`.
---
trace: [Tactic.evalRealRootCount] could not parse
      p
    as an explicit polynomial with rational coefficients
-/
#guard_msgs in
set_option trace.Tactic.evalRealRootCount true in
example (p : ℚ[X]) : Fintype.card (p.rootSet ℝ) = 1 := by eval_real_root_count

/--
error: unsolved goals
⊢ 2 = 1
-/
#guard_msgs in
example : Fintype.card ((X ^ 2 - 1 : ℚ[X]).rootSet ℝ) = 1 := by eval_real_root_count

/--
error: `simp` made no progress
---
trace: [Tactic.evalRealRootCount] could not parse
      p
    as an explicit polynomial with rational coefficients
-/
#guard_msgs in
set_option trace.Tactic.evalRealRootCount true in
example (p : ℚ[X]) : Fintype.card (p.rootSet ℝ) = 1 := by simp only [norm_real_root_count]
