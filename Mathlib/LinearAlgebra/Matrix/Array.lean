/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Batteries.Data.Fin.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# Array representation of matrices

This file relates `Fin`-indexed matrices to arrays of their entries in row-major ordering. This
 means that, for an `m` by `n` matrix, the entry at row `i` and column `j` can be found at
index `n * i + j` in the array.

## Main definitions

* `Matrix.ofArray A h`: The matrix with `m` rows and `n` columns whose entries are obtained from the
  array `A` of size `m * n` in row-major ordering.
* `Matrix.toArray A`: The array of entries of a matrix stored in row-major ordering.

## Implementation notes

The index in the array is computed using `Fin.mkDivMod` so that `Fin.divNat` and `Fin.modNat` can be
used to recover the matrix row and column from the array index.
-/

public section

namespace Matrix

variable {R : Type*}

/-- Construct a matrix from an array in row-major ordering. -/
def ofArray {m n : ℕ} (A : Array R) (hA : A.size = m * n) : Matrix (Fin m) (Fin n) R :=
  fun i j => A[Fin.mkDivMod i j]

@[simp]
theorem ofArray_apply {m n : ℕ} (A : Array R) (hA : A.size = m * n) (i : Fin m) (j : Fin n) :
    ofArray A hA i j = A[Fin.mkDivMod i j] := by
  simp [ofArray]

/-- The matrix constructed from the row-major array of `A`'s entries is `A`. -/
@[simp]
theorem ofArray_ofFn {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    ofArray (.ofFn fun k : Fin (m * n) ↦ A k.divNat k.modNat) Array.size_ofFn = A := by
  ext i j
  rw [ofArray_apply, Fin.getElem_fin, Array.getElem_ofFn, Fin.divNat_mkDivMod,
    Fin.modNat_mkDivMod]

/-- The array of the entries of a matrix in row-major ordering. -/
def toArray {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) : Array R :=
  .ofFn fun k : Fin (m * n) ↦ A k.divNat k.modNat

@[simp]
theorem size_toArray {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) : A.toArray.size = m * n :=
  Array.size_ofFn

@[simp]
theorem ofArray_toArray {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    ofArray A.toArray A.size_toArray = A :=
  ofArray_ofFn A

/-- The row-major array of the matrix constructed from an array is that array. -/
@[simp]
theorem toArray_ofArray {m n : ℕ} (A : Array R) (hA : A.size = m * n) :
    (ofArray A hA).toArray = A := by
  refine Array.ext (by simp [hA]) fun k hk hk' ↦ ?_
  simp [toArray, ofArray]

lemma ofArray_eq_of_getD [Zero R] {m n : ℕ} (A : Array R) (hA : A.size = m * n) :
    ofArray A hA = .of fun i j ↦ A.getD (n * i.val + j.val) 0 := by
  ext i j
  have : n * i.val + j.val < m * n := (Fin.mkDivMod i j).isLt
  simp [ofArray, hA, this]

end Matrix

end
