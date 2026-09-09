/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Basic

/-!

# Vandermonde's identity

In this file we prove Vandermonde's identity (`Nat.add_choose_eq`):
`(m + n).choose k = ∑ (i, j) ∈ antidiagonal k, m.choose i * n.choose j`

We follow the algebraic proof from
https://en.wikipedia.org/wiki/Vandermonde%27s_identity#Algebraic_proof .

-/

public section


open Polynomial Finset Finset.Nat

namespace Nat

/-- Vandermonde's identity -/
theorem add_choose_eq (m n k : ℕ) :
    (m + n).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2 := by
  calc
    (m + n).choose k = ((X + 1) ^ (m + n)).coeff k := by rw [coeff_X_add_one_pow, cast_id]
    _ = ((X + 1) ^ m * (X + 1) ^ n).coeff k := by rw [pow_add]
    _ = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2 := by
      rw [coeff_mul, Finset.sum_congr rfl]
      simp only [coeff_X_add_one_pow, cast_id, imp_true_iff]

/-- The sum of entries squared in a row of Pascal's triangle -/
theorem sum_range_choose_sq (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i) ^ 2 = (2 * n).choose n := by
  rw [two_mul, add_choose_eq, sum_antidiagonal_eq_sum_range_succ_mk]
  congr! 1 with _ h
  rw [choose_symm (Finset.mem_range_succ_iff.mp h), sq]

end Nat
