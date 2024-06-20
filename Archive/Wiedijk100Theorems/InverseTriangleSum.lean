/-
Copyright (c) 2020. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Yury Kudryashov
-/
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

#align_import wiedijk_100_theorems.inverse_triangle_sum from "leanprover-community/mathlib"@"5563b1b49e86e135e8c7b556da5ad2f5ff881cad"

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
theorem Theorems100.inverse_triangle_sum :
    ∀ n, ∑ k ∈ range n, (2 : ℚ) / (k * (k + 1)) = if n = 0 then 0 else 2 - (2 : ℚ) / n := by
  refine sum_range_induction _ _ (if_pos rfl) ?_
  rintro (_ | n)
  · rw [if_neg, if_pos] <;> norm_num
  simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.cast_succ]
  have A : (n + 1 + 1 : ℚ) ≠ 0 := by norm_cast
  field_simp
  ring
#align theorem_100.inverse_triangle_sum Theorems100.inverse_triangle_sum
