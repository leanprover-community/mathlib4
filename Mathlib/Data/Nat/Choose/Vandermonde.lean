import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!

# Vandermonde's identity

In this file we prove Vandermonde's identity (`Nat.add_choose_eq`):
`(m + n).choose k = ∑ (i, j) ∈ antidiagonal k, m.choose i * n.choose j`

We follow the algebraic proof from
https://en.wikipedia.org/wiki/Vandermonde%27s_identity#Algebraic_proof .

-/

public section


open Polynomial Finset Finset.Nat

/-- Vandermonde's identity -/
theorem Nat.add_choose_eq (m n k : ℕ) :
    (m + n).choose k = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2 := by
  calc
    (m + n).choose k = ((X + 1) ^ (m + n)).coeff k := by rw [coeff_X_add_one_pow, Nat.cast_id]
    _ = ((X + 1) ^ m * (X + 1) ^ n).coeff k := by rw [pow_add]
    _ = ∑ ij ∈ antidiagonal k, m.choose ij.1 * n.choose ij.2 := by
      rw [coeff_mul, Finset.sum_congr rfl]
      simp only [coeff_X_add_one_pow, Nat.cast_id, imp_true_iff]
