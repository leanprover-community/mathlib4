/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot

/-!
# Echelon decomposition certificates

`Echelon.Decomposition A L σ pivot` certifies an echelon decomposition of the matrix `A`.

## Main definitions

- `Echelon.Decomposition`: the certificate structure.

## Main results

- `Echelon.Decomposition.rank_eq`: `A.rank` is the pivot count of any certificate for `A`.
- `Echelon.Decomposition.prod_diag_mul_det`: `A.det` is determined by the diagonal products of
  `L` and of the echelon form of any certificate for `A`.

## Tags

matrix, echelon form
-/

public section

variable
  {m : Type*} [Fintype m] [LinearOrder m]
  {n : Type*} [Fintype n] [LinearOrder n]
  {R : Type*} [CommRing R]

namespace Echelon

open scoped Finset

/-- A certificate of an echelon form decomposition of `A`, certifying that
`L * (A.submatrix σ id)` is in echelon form with the pivot `pivot`, where `L`
is lower triangular with nonzero diagonal, and `σ` the permutation on the rows
of `A`.
This version does not take the final echelon form itself as it can be computed
from the other data.
-/
structure Decomposition (A : Matrix m n R) (L : Matrix m m R) (σ : Equiv.Perm m)
    (pivot : m → WithTop n) : Prop where
  isPivotedBy : (L * (A.submatrix σ id)).IsPivotedBy pivot
  L_lowerTriangular : L.IsLowerTriangular
  L_diag_ne_zero (i : m) : L.diag i ≠ 0

variable {A : Matrix m n R} {L : Matrix m m R} {σ : Equiv.Perm m} {pivot : m → WithTop n}

theorem Decomposition.prod_diag_mul_det {A : Matrix m m R} {pivot : m → WithTop m}
    (cert : Decomposition A L σ pivot) :
    (∏ i, L i i) * (Equiv.Perm.sign σ * A.det) = ∏ i, (L * A.submatrix σ id) i i := by
  rw [← Matrix.det_of_isLowerTriangular _ cert.L_lowerTriangular,
    ← cert.isPivotedBy.isRowEchelon.det_eq, Matrix.det_mul, Matrix.det_permute]

variable [IsDomain R]

theorem Decomposition.rank_eq (cert : Decomposition A L σ pivot) :
    A.rank = #{i | pivot i ≠ ⊤} := by
  rw [← cert.isPivotedBy.rank_eq,
    L.rank_mul_eq_right_of_isLowerTriangular _ cert.L_lowerTriangular cert.L_diag_ne_zero]
  exact (A.rank_submatrix σ (.refl _)).symm

end Echelon
