/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Hessenberg.Defs

/-!
# Hessenberg similarity certificates

`Hessenberg.Similarity A` certifies a similarity relation between the square matrix `A` and an upper
Hessenberg matrix.

## Main definitions

- `Hessenberg.Similarity`: the certificate structure.

## Main results

- `Hessenberg.Similarity.charpoly_eq`: The characteristic polynomial of `A` is equal to the
  characteristic polynomial of its Hessenberg matrix.
-/

public section

namespace Hessenberg

variable {m R : Type*} [CommRing R] [Fintype m] [DecidableEq m] [LinearOrder m] [SuccOrder m]

/-- A certificate of a Hessenberg similarity of `A` consisting of a permutation `σ` of its rows and
columns, a lower triangular matrix `L` with nonzero diagonal and an upper Hessenberg matrix `H`
satisfying `A.submatrix σ σ * L = L * H`.

NB: The certificate does not represent the standard Hessenberg reduction where the transformation
matrix `L` is orthogonal.
-/
structure Similarity (A : Matrix m m R) where
  /-- The transformation matrix. -/
  L : Matrix m m R
  /-- The row / column permutation on `A`. -/
  σ : Equiv.Perm m
  /-- The upper Hessenberg matrix. -/
  H : Matrix m m R
  mul_eq_mul : A.reindex σ σ * L = L * H
  isLowerTriangular : L.IsLowerTriangular
  diag_ne_zero (i : m) : L.diag i ≠ 0
  isUpperHessenberg: H.IsUpperHessenberg

@[simp]
theorem Similarity.charpoly_eq [IsDomain R] {A : Matrix m m R} (cert : Similarity A) :
    cert.H.charpoly = A.charpoly :=
  calc cert.H.charpoly = (A.reindex cert.σ cert.σ).charpoly :=
        (Matrix.charpoly_eq_of_mul_eq_mul
          (cert.isLowerTriangular.det_ne_zero cert.diag_ne_zero) cert.mul_eq_mul).symm
    _ = A.charpoly :=
      Matrix.charpoly_reindex cert.σ A

end Hessenberg

end
