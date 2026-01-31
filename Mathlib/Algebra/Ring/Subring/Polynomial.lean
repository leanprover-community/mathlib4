/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Polynomials over subrings

Given a field `K` with a subring `R`, in this file we construct a map from polynomials in `K[X]`
with coefficients in `R` to `R[X]`. We provide several lemmas to deal with coefficients, degree, and
evaluation of `Polynomial.toSubring`. This is useful when dealing with integral elements in an
extension of fields.

## Main definitions

* `Polynomial.toSubring` : given a polynomial `P` in `K[X]` whose coefficients all belong to a
  subring `R` of the field `K`, `P.toSubring R` is the corresponding polynomial in `R[X]`.
-/

@[expose] public section

variable {K L : Type*} [Field K] (R : Subring K)

open scoped Polynomial

/-- Given a polynomial in `K[X]` such that all coefficients belong to the subring `R`,
  `Polynomial.toSubring` is the corresponding polynomial in `R[X]`. -/
def Polynomial.toSubring (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R) : R[X] where
  toFinsupp :=
  { support := P.support
    toFun := fun n => ⟨P.coeff n, hP n⟩
    mem_support_toFun := fun n => by
      rw [ne_eq, ← Subring.coe_eq_zero_iff, mem_support_iff] }

namespace Polynomial

variable (P : K[X]) (hP : ∀ n : ℕ, P.coeff n ∈ R)

@[simp]
theorem toSubring_coeff (n : ℕ) : ↑((P.toSubring R hP).coeff n) = P.coeff n := rfl

@[simp]
theorem toSubring_leadingCoeff : ↑(P.toSubring R hP).leadingCoeff = P.leadingCoeff := rfl

@[simp]
theorem toSubring_monic_iff : (P.toSubring R hP).Monic ↔ P.Monic := by
  rw [Monic, Monic, ← toSubring_leadingCoeff, OneMemClass.coe_eq_one]

@[simp]
theorem toSubring_natDegree : (P.toSubring R hP).natDegree = P.natDegree := rfl

variable [Field L] [Algebra K L]

@[simp]
theorem toSubring_eval₂ (x : L) : eval₂ (algebraMap R L) x (P.toSubring R hP) = aeval x P := by
  rw [aeval_eq_sum_range, eval₂_eq_sum_range]
  exact Finset.sum_congr rfl (fun n _ => by rw [Algebra.smul_def]; rfl)

end Polynomial
