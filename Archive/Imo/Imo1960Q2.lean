/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.Real.Sqrt

/-!
# IMO 1960 Q2

For what values of the variable $x$ does the following inequality hold:

\[\dfrac{4x^2}{(1 - \sqrt {2x + 1})^2} < 2x + 9 \ ?\]

We follow solution at
[Art of Problem Solving](https://artofproblemsolving.com/wiki/index.php/1960_IMO_Problems/Problem_2)
with minor modifications.
-/

open Real Set

namespace Imo1960Q2

/-- The predicate says that `x` satisfies the inequality

\[\dfrac{4x^2}{(1 - \sqrt {2x + 1})^2} < 2x + 9\]

and belongs to the domain of the function on the left-hand side.
-/
@[mk_iff isGood_iff']
structure IsGood (x : ℝ) : Prop where
  /-- The number satisfies the inequality. -/
  ineq : 4 * x ^ 2 / (1 - sqrt (2 * x + 1)) ^ 2 < 2 * x + 9
  /-- The number belongs to the domain of \(\sqrt {2x + 1}\). -/
  sqrt_dom : 0 ≤ 2 * x + 1
  /-- The number belongs to the domain of the denominator. -/
  denom_dom : (1 - sqrt (2 * x + 1)) ^ 2 ≠ 0

/-- Solution of IMO 1960 Q2: solutions of the inequality
are the numbers of the half-closed interval \([-1/2, 45/8)\) except for the number zero. -/
theorem isGood_iff {x} : IsGood x ↔ x ∈ Ico (-1/2) (45/8) \ {0} := by
  -- First, note that the denominator is equal to zero at `x = 0`, hence it's not a solution.
  rcases eq_or_ne x 0 with rfl | hx
  · simp [isGood_iff']
  cases lt_or_le x (-1/2) with
  | inl hx2 =>
    -- Next, if `x < -1/2`, then the square root is undefined.
    have : 2 * x + 1 < 0 := by linarith
    simp [hx2.not_le, isGood_iff', this.not_le]
  | inr hx2 =>
    -- Now, if `x ≥ -1/2`, `x ≠ 0`, then the expression is well-defined.
    have hx2' : 0 ≤ 2 * x + 1 := by linarith
    have H : 1 - sqrt (2 * x + 1) ≠ 0 := by
      rw [sub_ne_zero, ne_comm, ne_eq, sqrt_eq_iff_sq_eq hx2' zero_le_one]
      simpa
    calc
      -- Note that the fraction in the LHS is equal to `(1 + sqrt (2 * x + 1)) ^ 2`
      IsGood x ↔ (1 + sqrt (2 * x + 1)) ^ 2 < 2 * x + 9 := by
        have : 4 * x ^ 2 = (1 + sqrt (2 * x + 1)) ^ 2 * (1 - sqrt (2 * x + 1)) ^ 2 := by
          rw [← mul_pow, ← sq_sub_sq, sq_sqrt hx2']
          ring
        simp [isGood_iff', *]
      -- Simplify the inequality
      _ ↔ sqrt (2 * x + 1) < 7 / 2 := by
        rw [add_sq, sq_sqrt hx2']; constructor <;> intro <;> linarith
      _ ↔ 2 * x + 1 < (7 / 2) ^ 2 := sqrt_lt' <| by positivity
      _ ↔ x < 45 / 8 := by constructor <;> intro <;> linarith
      _ ↔ x ∈ Ico (-1/2) (45/8) \ {0} := by simp [*]
