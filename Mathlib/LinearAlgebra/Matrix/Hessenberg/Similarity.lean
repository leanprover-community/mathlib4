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

variable {n : ℕ} {R : Type*} [CommRing R]

/-- A certificate of a Hessenberg similarity of `A` consisting of a permutation `σ` of its rows and
columns and a lower triangular transform `L` with nonzero diagonal satisfying `A.submatrix σ σ * L =
L * H` where the upper Hessenberg form `H` is stored as an array of entries, `Harr`, stored in
row-major order.
-/
structure Similarity (A : Matrix (Fin n) (Fin n) R) where
  /-- The transformation matrix. -/
  L : Matrix (Fin n) (Fin n) R
  /-- The row / column permutation on `A`. -/
  σ : Equiv.Perm (Fin n)
  /-- The entries of the upper Hessenberg matrix in row-major order. -/
  Harr : Array R
  size_eq : Harr.size = n * n
  similarity : A.submatrix σ σ * L = L * Matrix.ofArray Harr size_eq
  L_lowerTriangular : L.IsLowerTriangular
  L_diag_ne_zero (i : Fin n) : L.diag i ≠ 0
  hessenberg : (Matrix.ofArray Harr size_eq).IsUpperHessenberg

theorem Similarity.charpoly_eq [IsDomain R] {A : Matrix (Fin n) (Fin n) R} (cert : Similarity A) :
    A.charpoly = (Matrix.ofArray cert.Harr cert.size_eq).charpoly :=
  calc A.charpoly = (A.submatrix cert.σ cert.σ).charpoly :=
        (Matrix.charpoly_submatrix_equiv_self cert.σ A).symm
    _ = (Matrix.ofArray cert.Harr cert.size_eq).charpoly :=
        Matrix.charpoly_eq_of_mul_eq_mul
          (cert.L_lowerTriangular.det_ne_zero cert.L_diag_ne_zero) cert.similarity

end Hessenberg

end
