/-
Copyright (c) 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring

/-!
# Sum of the Reciprocals of the Triangular Numbers

This file proves Theorem 42 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

We interpret “triangular numbers” as naturals of the form $\frac{k(k+1)}{2}$ for natural `k`.
We prove that the sum of the reciprocals of the first `n` triangular numbers is $2 - \frac2n$.

## Tags

discrete_sum
-/


open Finset

/-- **Sum of the Reciprocals of the Triangular Numbers** -/
theorem Theorems100.inverse_triangle_sum (n : ℕ) :
    ∑ k ∈ range n, (2 : ℚ) / (k * (k + 1)) = if n = 0 then 0 else 2 - (2 : ℚ) / n := by
  apply sum_range_induction _ _ rfl
  rintro (_ | _)
  · norm_num
  · field_simp
    ring_nf
    simp
