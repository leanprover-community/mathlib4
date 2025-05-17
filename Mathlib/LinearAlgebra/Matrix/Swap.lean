/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Matrix.PEquiv

/-!
# Swap matrices

A swap matrix indexed by `i` and `j` is the matrix that, when multiplying another matrix
on the left (resp. on the right), swaps the `i`-th row with the `j`-th row
(resp. the `i`-th column with the `j`-th column).

Swap matrices are a special case of *elementary matrices*. For transvections see
`Mathlib/LinearAlgebra/Matrix/Transvection.lean`.

## Implementation detail

This is a thin wrapper around `(Equiv.swap i j).permMatrix`.
-/

namespace Matrix

section Def
variable {R n : Type*} [Zero R] [One R] [DecidableEq n]

variable (R) in
/-- The swap matrix `swap R i j` is the identity matrix with the
`i`-th and `j`-th rows modified such that multiplying by it on the
left (resp. right) corresponds to swapping the `i`-th and `j`-th row (resp. column). -/
def swap (i j : n) : Matrix n n R :=
  (Equiv.swap i j).permMatrix R

lemma swap_comm (i j : n) :
    swap R i j = swap R j i := by
  simp only [swap, Equiv.swap_comm]

@[simp]
lemma transpose_swap (i j : n) : (swap R i j).transpose = swap R i j := by
  simp [swap]

@[simp]
lemma conjTranspose_swap {R : Type*} [NonAssocSemiring R] [StarRing R] (i j : n) :
    (swap R i j).conjTranspose = swap R i j := by
  simp [swap]

end Def

section
variable {R n m : Type*} [Semiring R] [DecidableEq n]

@[simp]
lemma map_swap {S : Type*} [NonAssocSemiring S] (f : R →+* S) (i j : n) :
    (swap R i j).map f = swap S i j := by
  simp [swap]

variable [Fintype n]

lemma swap_mulVec (i j : n) (a : n → R) :
    swap R i j *ᵥ a = a ∘ Equiv.swap i j := by
  simp [swap, PEquiv.toMatrix_toPEquiv_mulVec]

lemma vecMul_swap (i j : n) (a : n → R) :
    a ᵥ* swap R i j = a ∘ Equiv.swap i j := by
  simp [swap, PEquiv.vecMul_toMatrix_toPEquiv]

@[simp]
lemma swap_mulVec_apply (i j : n) (a : n → R) :
    (swap R i j *ᵥ a) i = a j := by
  simp [swap, PEquiv.toMatrix_toPEquiv_mulVec]

@[simp]
lemma vecMul_swap_apply (i j : n) (a : n → R) :
    (a ᵥ* swap R i j) i = a j := by
  simp [swap, PEquiv.vecMul_toMatrix_toPEquiv]

/-- Multiplying with `swap R i j` on the left swaps the `i`-th row with the `j`-th row. -/
@[simp]
lemma swap_mul_apply_left (i j : n) (a : m) (g : Matrix n m R) :
    (swap R i j * g) i a = g j a := by
  simp [swap, PEquiv.toMatrix_toPEquiv_mul]

/-- Multiplying with `swap R i j` on the left swaps the `j`-th row with the `i`-th row. -/
@[simp]
lemma swap_mul_apply_right (i j : n) (a : m) (g : Matrix n m R) :
    (swap R i j * g) j a = g i a := by
  rw [swap_comm, swap_mul_apply_left]

lemma swap_mul_of_ne {i j a : n} {b : m} (hai : a ≠ i) (haj : a ≠ j) (g : Matrix n m R) :
    (swap R i j * g) a b = g a b := by
  simp [swap, PEquiv.toMatrix_toPEquiv_mul, Equiv.swap_apply_of_ne_of_ne hai haj]

/-- Multiplying with `swap R i j` on the right swaps the `i`-th column with the `j`-th column. -/
@[simp]
lemma mul_swap_apply_left (i j : n) (a : m) (g : Matrix m n R) :
    (g * swap R i j) a i = g a j := by
  simp [swap, PEquiv.mul_toMatrix_toPEquiv]

/-- Multiplying with `swap R i j` on the right swaps the `j`-th column with the `i`-th column. -/
@[simp]
lemma mul_swap_apply_right (i j : n) (a : m) (g : Matrix m n R) :
    (g * swap R i j) a j = g a i := by
  rw [swap_comm, mul_swap_apply_left]

lemma mul_swap_of_ne {i j b : n} {a : m} (hbi : b ≠ i) (hbj : b ≠ j) (g : Matrix m n R) :
    (g * swap R i j) a b = g a b := by
  simp [swap, PEquiv.mul_toMatrix_toPEquiv, Equiv.swap_apply_of_ne_of_ne hbi hbj]

/-- Swap matrices are self inverse. -/
lemma swap_mul_self (i j : n) : swap R i j * swap R i j = 1 := by
  simp only [swap]
  rw [← Equiv.swap_inv, Equiv.Perm.inv_def]
  simp [← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_trans]

end

namespace GeneralLinearGroup
variable (R : Type*) {n : Type*} [CommRing R] [DecidableEq n] [Fintype n]

/-- `Matrix.swap` as an element of `GL n R`. -/
@[simps]
def swap (i j : n) : GL n R where
  val := Matrix.swap R i j
  inv := Matrix.swap R i j
  val_inv := swap_mul_self i j
  inv_val := swap_mul_self i j

variable {R} {S : Type*} [CommRing S] (f : R →+* S)

@[simp]
lemma map_swap (i j : n) : (swap R i j).map f = swap S i j := by
  ext : 1
  simp [swap]

end GeneralLinearGroup

end Matrix
