/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic


/-!
# An exact-division algorithm for echelon form

This file defines an implementation of Bareiss algorithm which derives the echelon form of a matrix
using exact divisions to avoid exponential explosion in the sizes of intermediate elements.

The certificate is constructed from verifying the final matrix multiplication instead of the
computation trace to allow eventual optimisation using fast matrix multiplication that requires
only O(n^2) kernel steps.

The algorithm itself runs in O(n^3), with the bit-sizes of the elements growing in O(n). However,
this is not the performance bottleneck since the computation part runs in metaprogramming.


## Main definitions


## Main lemmas

The lemmas in this file are unfolding equations.

## Tags

matrix, echelon form, Bareiss

-/

@[expose] public section

universe v

variable {m n : ℕ}
variable {R : Type v} {M : Matrix (Fin m) (Fin n) R}

namespace Bareiss

variable [CommRing R] [IsDomain R]

/-- The result returned by the Bareiss algorithm. -/
structure Decomposition (M : Matrix (Fin m) (Fin n) R) where
  L : Matrix (Fin m) (Fin m) R
  σ : Equiv.Perm (Fin m)
  pivot : List (Fin n)
  is_pivot : (L * (M.submatrix σ id)).IsPivot pivot
  L_lowerTriangular : L.BlockTriangular OrderDual.toDual
  L_diag_ne_zero : ∀ i, L i i ≠ 0

theorem Decomposition.rank_eq (cert : Decomposition M) :
  M.rank = cert.pivot.length :=
  cert.is_pivot.rank_eq_of_lowerTriangular cert.L_lowerTriangular cert.L_diag_ne_zero

end Bareiss
