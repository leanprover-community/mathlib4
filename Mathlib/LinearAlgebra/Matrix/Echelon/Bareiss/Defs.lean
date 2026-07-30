/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot


/-!
# Bareiss decomposition certificates

`Bareiss.Decomposition` certifies an echelon decomposition of a matrix `A`: pivots for
`L * (A.submatrix σ id)` with `L` lower triangular with nonzero diagonal and `σ` a row
permutation, together with the pivot count. The certificate records the decomposed form
rather than a computation trace, so a producer is free to choose how to find it.

## Main definitions

- `Bareiss.Decomposition`: the certificate structure.

## Main results

- `Bareiss.Decomposition.rank_eq`: `A.rank` is the pivot count of any certificate for `A`.

## Tags

matrix, echelon form, Bareiss
-/

@[expose] public section

universe v

variable {m n : ℕ}
variable {R : Type v} {A : Matrix (Fin m) (Fin n) R}

namespace Bareiss

open Finset

variable [CommRing R] [IsDomain R]

/-- The result returned by the Bareiss algorithm. -/
structure Decomposition (A : Matrix (Fin m) (Fin n) R) where
  /-- The lower-triangular transform. -/
  L : Matrix (Fin m) (Fin m) R
  /-- The row permutation. -/
  σ : Equiv.Perm (Fin m)
  /-- The pivot column of each row of the final echelon form. -/
  pivot : Fin m → WithTop (Fin n)
  /-- The rank: the number of rows with a pivot. -/
  rank : ℕ
  isPivotedBy : (L * (A.submatrix σ id)).IsPivotedBy pivot
  card_eq : #{i | pivot i ≠ ⊤} = rank
  L_lowerTriangular : L.IsLowerTriangular
  L_diag_ne_zero (i : Fin m) : L.diag i ≠ 0

theorem Decomposition.rank_eq (cert : Decomposition A) :
    A.rank = cert.rank := by
  have hr : (A.submatrix cert.σ id).rank = A.rank := A.rank_submatrix cert.σ (Equiv.refl (Fin n))
  rw [← hr, ← Matrix.rank_mul_eq_right_of_isLowerTriangular cert.L _ cert.L_lowerTriangular
    cert.L_diag_ne_zero, cert.isPivotedBy.rank_eq, cert.card_eq]

end Bareiss
