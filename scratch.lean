import Mathlib

import Mathlib.Tactic.Algebra


section Polynomial
open Polynomial

example (x : ℚ) :
    (X + 2) * (X + C x) = X * X + C (2 + x) * X + C (2 * x) := by
  simp_rw [← Polynomial.algebraMap_eq, Algebra.algebraMap_eq_smul_one]
  algebra with ℚ


end Polynomial

section MvPolynomial
open MvPolynomial

example (x : ℚ) :
    (X 1 + 2) * (X 1 + C x) = X 1 * X 1 + C (2 + x) * X 1 + C (2 * x) := by
  simp_rw [← MvPolynomial.algebraMap_eq, Algebra.algebraMap_eq_smul_one]
  algebra with ℚ

example (x : ℚ) :
    (X 1 + 2) * (X 1 + C x) = 0 := by
  simp_rw [← MvPolynomial.algebraMap_eq, Algebra.algebraMap_eq_smul_one]
  algebra_nf with ℚ
  simp only [smul_eq_C_mul, mul_one]
  sorry

end MvPolynomial
