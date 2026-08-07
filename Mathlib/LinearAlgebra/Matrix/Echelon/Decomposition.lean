/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot

/-!
# Echelon decomposition certificates

`Echelon.Decomposition A` certifies an echelon decomposition of the matrix `A`.

## Main definitions

- `Echelon.Decomposition`: the certificate structure.

## Main results

- `Echelon.Decomposition.rank_eq`: `A.rank` is the pivot count of any certificate for `A`.

## Tags

matrix, echelon form
-/

@[expose] public section

universe v

variable {m n : ℕ}
variable {R : Type v} {A : Matrix (Fin m) (Fin n) R}

namespace Echelon

open Finset

variable [CommRing R] [IsDomain R]

/-- A certificate of an echelon form decomposition of `A`, certifying that
`L * (A.submatrix σ id)` is in echelon form by providing a pivot, where `L`
is lower triangular with nonzero diagonal, and `σ` the permutation on the rows
of `A`.
This version does not store the final echelon form itself as it can be computed
by the data enclosed.
-/
structure Decomposition (A : Matrix (Fin m) (Fin n) R) where
  L : Matrix (Fin m) (Fin m) R
  σ : Equiv.Perm (Fin m)
  pivot : Fin m → WithTop (Fin n)
  isPivotedBy : (L * (A.submatrix σ id)).IsPivotedBy pivot
  L_lowerTriangular : L.IsLowerTriangular
  L_diag_ne_zero (i : Fin m) : L.diag i ≠ 0

theorem Decomposition.rank_eq (cert : Decomposition A) :
    A.rank = #{i | cert.pivot i ≠ ⊤} := by
  rw [← cert.isPivotedBy.rank_eq,
    cert.L.rank_mul_eq_right_of_isLowerTriangular _ cert.L_lowerTriangular cert.L_diag_ne_zero]
  exact (A.rank_submatrix cert.σ (.refl _)).symm

end Echelon
