/-
Copyright (c) 2024 Mark Santa Clara Munro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Santa Clara Munro, Christopher Lynch
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.RowCol

/-!
# Elementary Row Operations

This file introduces all elementary row operations, elementary matrices, and some important
statements that come with them. The three main theorems proved for each elemetary row operation are
the folllowing:

1. Each row operation is equivalent to a multiplication by an elementary matrix.
2. Each row operation has another row operations which inverts it.
3. Each elementary matrix has a left inverse.

## Main definitions

- `swapRow`: A row is swapped with another row.
- `mulRow`: A row is multiplied by a non-zero constant, also known as scaling a row.
- `addMulRow`: A multiple of another row is added to the row.
- `swapRowElemMat`: Elementary matrix that comes from one operation `swapRow`.
- `mulRowElemMat`: Elementary matrix that comes from one operation `mulRow`.
- `addMulRowElemMat`: Elementary matrix that comes from one operation `addMulRow`.

## Main statements

- `swapRow_elem_inv`: `swapRowElemMat` has a left inverse.
- `mulRow_elem_inv`: `mulRowElemMat` has a left inverse.
- `addMulRow_elem_inv`: `addMulRowElemMat` has a left inverse.

## Implementation Notes

- type variable `m` is used for rows
- type variable `n` is used for columns
- type variable `α` is used for the entries of the matrix
- type variable `R` is used for scalar multiplication on matrices
- variables `i`, `j`, and `k` are used to represent rows
- variable `l` is used to represent columns
- variable `x` is used to represent a scalar
- variables `y` and `z` are used in ext and intro cases

## Tags

matrix, elementary matrices, matrix operations, elementary row operations, linear algebra
-/

variable {m n α R : Type*}
variable [DecidableEq m]

open Matrix

namespace Matrix

section swapRow

/-! ### Declarations about `swapRow` -/

/-- Replaces the `i`th row of matrix `M` with the values of row `j`. -/
def dupRow (M : Matrix m n α) (i : m) (j : m) : Matrix m n α :=
  updateRow M i (M j)

/-- Swaps the `i`th row of matrix `M` with row `j`. -/
def swapRow (M : Matrix m n α) (i : m) (j : m) : Matrix m n α :=
  updateRow (dupRow M i j) j (M i)

/-- Swaps the `i`th row of identity matrix with row `j`, resulting in an elementary matrix-/
def swapRowElemMat [One α] [Zero α] (i : m) (j : m) : Matrix m m α :=
  swapRow (1 : Matrix m m α) i j

/-! ### Basic properties of swapRow -/

/-- Row `i` of matrix `M` will be the previous row `j` after swapping rows `i` and `j`. -/
@[simp]
lemma swapRow_eq_first (M : Matrix m n α) (i : m) (j : m) :
    swapRow M i j i = M j := by
  rw [swapRow, dupRow]
  by_cases sameRow : i = j
  · rw [sameRow, Matrix.updateRow_self]
  · rw [Matrix.updateRow_ne, Matrix.updateRow_self]; exact sameRow

/-- Row `j` of matrix `M` will be the previous row `i` after swapping rows `i` and `j`. -/
@[simp]
lemma swapRow_eq_second (M : Matrix m n α) (i : m) (j : m) :
    swapRow M i j j = M i := by
  rw [swapRow, dupRow]
  by_cases sameRow : j = i
  · rw [sameRow, Matrix.updateRow_self]
  · rw [Matrix.updateRow_self]

/-- Some row `k` of matrix `M` will remain unchanged after swapping rows `i` and `j`. -/
@[simp]
lemma swapRow_other_rows_same (M : Matrix m n α) (i : m) (j : m) (k : m) (h₁ : k ≠ i) (h₂ : k ≠ j) :
    swapRow M i j k = M k := by
  rw [swapRow, dupRow, Matrix.updateRow_ne, Matrix.updateRow_ne]; repeat assumption

/-- Swapping rows `i` and `j` of matrix `M` is equivalent to swapping row `j` with row `i`. -/
lemma swapRow_comm (M : Matrix m n α) (i : m) (j : m) :
    swapRow M i j = swapRow M j i := by
  rw [← Matrix.ext_iff]
  intro y z
  by_cases h₁ : y = i
  · rw [h₁, swapRow_eq_second, swapRow_eq_first]
  · by_cases h₂ : y = j
    · rw [h₂, swapRow_eq_first, swapRow_eq_second]
    · rw [swapRow_other_rows_same, swapRow_other_rows_same]; repeat assumption

/-! ### swapRow has a row operations which inverts it -/

/-- Swapping rows `i` and `j` of matrix `M` twice will return the original matrix `M`. -/
@[simp]
theorem swapRow_involutive (M : Matrix m n α) (i : m) (j : m) :
    swapRow (swapRow M i j) i j = M := by
  rw [← Matrix.ext_iff]
  intro y z
  by_cases h₁ : y = i
  · rw [h₁, swapRow_eq_first, swapRow_eq_second]
  · by_cases h₂ : y = j
    · rw [h₂, swapRow_eq_second, swapRow_eq_first]
    · rw [swapRow_other_rows_same, swapRow_other_rows_same]; repeat assumption

/-! ### swapRow is equivalent to a multiplication by the elementary matrix -/

/-- Multiplying matrix `M` by the elementary matrix derived from swapping rows `i` and `j` of the
identity matrix is equivalent to swapping rows `i` and `j` of matrix `M`. -/
@[simp]
theorem swapRowElemMat_eq_swapRow [Fintype m] [NonAssocSemiring α] (M : Matrix m m α) (i : m)
    (j : m) :
    swapRowElemMat i j * M = swapRow M i j := by
  rw [swapRowElemMat]
  ext y z
  by_cases h₁ : y = i
  · rw [h₁, swapRow_eq_first, mul_apply, swapRow_eq_first]
    simp_rw [one_apply]
    simp
  · by_cases h₂ : y = j
    · rw [h₂, swapRow_eq_second, mul_apply, swapRow_eq_second]
      simp_rw [one_apply]
      simp
    · rw [swapRow_other_rows_same, mul_apply, swapRow_other_rows_same]
      · simp_rw [one_apply]
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      repeat assumption

/-! ### swapRow elementary matrix has a left inverse -/

/-- Multiplying the elementary matrix derived from swapping rows `i` and `j` of the identity matrix
by itself reverts it to the identity matrix. `swapRowElemMat` is it's own inverse. -/
theorem swapRow_elem_inv [Fintype m] [NonAssocSemiring α] (i : m) (j : m) :
    swapRowElemMat i j * swapRowElemMat i j = (1 : Matrix m m α) := by
  rw [swapRowElemMat_eq_swapRow, swapRowElemMat, swapRow_involutive]

end swapRow

section mulRow

/-! ### Declarations about `mulRow` -/

/-- Multiplies the `i`th row of matrix `M` by scalar `x`. -/
def mulRow [SMul R α] (M : Matrix m n α) (i : m) (x : R) : Matrix m n α :=
  updateRow M i (x • M i)

/-- Multiplies the `i`th row of identity matrix by scalar `x`, resulting in an elementary matrix -/
def mulRowElemMat [SMul R α] [One α] [Zero α] (i : m) (x : R) : Matrix m m α :=
  mulRow (1 : Matrix m m α) i x

/-! ### Basic properties of mulRow -/

/-- Row `i` of matrix `M` will be scaled by `x` after multiplying row `i` by scalar `x`. -/
@[simp]
lemma mulRow_eq_mul_row [SMul R α] (M : Matrix m n α) (i : m) (x : R) :
    mulRow M i x i = x • M i := by
  rw [mulRow, updateRow_self]

/-- Some row `j` of matrix `M` will remain unchanged after multiplying row `i` by scalar `x`. -/
@[simp]
lemma mulRow_other_rows_same [SMul R α] (M : Matrix m n α) (i : m) (j : m) (h₁ : j ≠ i) (x : R) :
    mulRow M i x j = M j := by
  rw [mulRow, updateRow_ne]; exact h₁

/-! ### mulRow has a row operations which inverts it -/

/-- Multiplying row `i` of matrix `M` by a scalar `x` and then by `x`'s multiplicative
inverse will return the original matrix `M`. -/
@[simp]
theorem mulRow_mulRow_inv_cancel_left [Group R] [MulAction R α] (M : Matrix m n α) (i : m) (x : R) :
    mulRow (mulRow M i x) i (x⁻¹) = M := by
  unfold mulRow
  ext y z
  by_cases h : y = i
  · rw [h]
    repeat rw [updateRow_self]
    simp
  · repeat rw [updateRow_ne h]

/-! ### mulRow is equivalent to a multiplication by the elemetary matrix -/

/-- Multiplying matrix `M` by the elementary matrix derived from multiplying row `i` of the
identity matrix by scalar `x` is equivalent to multiplying row `i` of matrix `M` by scalar `x` -/
@[simp]
theorem mulRowElemMat_eq_mulRow [Fintype m] [Monoid R] [NonAssocSemiring α]
    [DistribMulAction R α] [IsScalarTower R α α] (M : Matrix m m α)
    (i : m) (x : R) :
    (mulRowElemMat i x) * M = mulRow M i x := by
  rw [mulRowElemMat]
  ext y z
  by_cases h : y = i
  · rw [h, mulRow_eq_mul_row, mul_apply, mulRow_eq_mul_row]
    simp only [Pi.smul_apply]
    simp_rw [one_apply]
    simp
  · rw [mulRow_other_rows_same, mul_apply, mulRow_other_rows_same]
    · simp_rw [one_apply]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    repeat exact h

/-! ### mulRow elementary matrix has a left inverse -/

/-- The elementary matrix  derived from multiplying row `i` of the identity matrix by scalar `x` has
a left inverse. -/
theorem mulRow_elem_inv [Fintype m] [Group R] [NonAssocSemiring α] [DistribMulAction R α]
    [IsScalarTower R α α]
    (i : m) (x : R) :
    mulRowElemMat i x⁻¹ * mulRowElemMat i x = (1 : Matrix m m α) := by
  rw [mulRowElemMat_eq_mulRow, mulRowElemMat, mulRow_mulRow_inv_cancel_left]

end mulRow

section addMulRow

/-! ### Declarations about `addMulRow` -/

/-- Adds the `j`th row of matrix `M` times scalar `x` to row `i`. -/
def addMulRow [SMul R α] [Add α] (M : Matrix m n α) (i : m) (j : m) (x : R): Matrix m n α :=
  updateRow M i (M i + x • M j)

/-- Adds the `j`th row of the identity matrix times scalar `x` to row `i`, resulting in an
elementary matrix. -/
def addMulRowElemMat [SMul R α] [Add α] [One α] [Zero α] (i : m) (j : m) (x : R) : Matrix m m α :=
  addMulRow (1 : Matrix m m α) i j x

/-! ### Basic properties of addMulRow -/

/-- Row `i` of matrix `M` will be the result of adding row `j` times scalar `x` to the original
row `i` after adding row `j` times scalar `x` to row `i`. -/
@[simp]
lemma addMulRow_eq_add_mul_row [SMul R α] [Add α] (M : Matrix m n α) (i : m) (j : m) (x : R) :
    addMulRow M i j x i = M i + x • M j := by
  rw [addMulRow]
  by_cases h : i = j
  · rw [h, updateRow_self]
  · rw [updateRow_self]

/-- Some row `k` of matrix `M` will remain unchanged after adding row `j` times scalar `x` to
row `i`. -/
@[simp]
lemma addMulRow_other_rows_same [SMul R α] [Add α] (M : Matrix m n α) (i : m) (j : m) (k : m)
    (h₁ : k ≠ i) (x : R) :
    addMulRow M i j x k = M k := by
  rw [addMulRow]
  rw [updateRow_ne h₁]

/-! ### addMulRow has a row operations which inverts it -/

/-- Adding row `j` of matrix `M` times scalar `x` to row `i` and then adding row `j` times `-x` to
row `i` will return the original matrix `M`. -/
@[simp]
theorem addMulRow_addMulRow_neg_cancel_left [Ring R] [AddCommGroup α] [Module R α]
    (M : Matrix m n α) (i : m) (j : m) (h₁ : j ≠ i) (x : R) :
    addMulRow (addMulRow M i j x) i j (-x) = M := by
  unfold addMulRow
  ext y z
  by_cases h : y = i
  · rw [h]
    repeat rw [updateRow_self]
    rw [updateRow_ne]
    · simp only [neg_smul, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, add_neg_cancel_right]
    exact h₁
  · repeat rw [updateRow_ne h]

/-! ### addMulRow is equivalent to a multiplication by the elementary matrix -/

/-- Multiplying matrix `M` by the elementary matrix derived from adding row `j` of the identity
matrix times scalar `x` to row `i` of the identity matrix is equivalent to adding row `j` of matrix
`M` times scalar `x` to row `i` of matrix `M`. -/
@[simp]
theorem addMulRowElemMat_eq_addMulRow [Fintype m] [NonAssocSemiring α] [SMulZeroClass R α]
    [IsScalarTower R α α]
    (M : Matrix m m α) (i : m) (j : m) (x : R) :
    (addMulRowElemMat i j x) * M = addMulRow M i j x := by
  rw [addMulRowElemMat]
  ext y z
  by_cases h : y = i
  · rw [h, addMulRow_eq_add_mul_row, mul_apply, addMulRow_eq_add_mul_row]
    simp only [Pi.add_apply, Pi.smul_apply]
    simp_rw [one_apply]
    simp [add_mul]
    rw [Finset.sum_add_distrib]
    simp
  · rw [addMulRow_other_rows_same]
    · rw [mul_apply, addMulRow_other_rows_same]
      · simp_rw [one_apply]
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      assumption
    repeat assumption

/-! ### addMulRow elementary matrix has a left inverse -/

/-- The elementary matrix derived from adding row `j` of the identity matrix times scalar `x` to
row `i` has a left inverse. -/
theorem addMulRow_elem_inv [Fintype m] [Ring R] [NonAssocRing α] [Module R α]
    [IsScalarTower R α α]
    (i : m) (j: m) (x : R) (h₁ : j ≠ i) :
    addMulRowElemMat i j (-x) * addMulRowElemMat i j x = (1 : Matrix m m α) := by
  rw [addMulRowElemMat_eq_addMulRow, addMulRowElemMat, addMulRow_addMulRow_neg_cancel_left]
  exact h₁

end addMulRow

end Matrix
