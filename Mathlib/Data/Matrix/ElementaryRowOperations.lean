/-
Copyright (c) 2024 Mark Santa Clara Munro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Santa Clara Munro, Christopher Lynch
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Real.Basic

/-!
# Elementary Row Operations



## Main definitions

- `swapRow`: A row is swaped with another row.
- `mulRow`: A row is multiplied by a non-zero constant, also known as scaling a row.
- `addMulRow`: A multiple of another row is added to the row.

## Main statements

-

## Implementation Notes

- type variable `m` is used for rows
- type variable `n` is used for columns
- type variable `α` is used for the entries of the matrix
- type variable `R` is used for scalar multiplication on matrices
- variables `i`, `j`, and `k` are used to represent rows
- variable `l` is used to represent columns
- variable `x` is used to represent a scalar

## References

<https://en.wikipedia.org/wiki/Elementary_matrix>

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
def swapRow_elem_mat [One α] [Zero α] (i : m) (j : m) : Matrix m m α :=
  swapRow (1 : Matrix m m α) i j

/-! ### Basic properties of swapRow -/

/-- Row `i` of matrix `M` will be the previous row `j` after swapping rows `i` and `j`. -/
@[simp]
lemma swapRow_eq_first (M : Matrix m n α) (i : m) (j : m) :
    swapRow M i j i = M j := by
  rw [swapRow, dupRow]
  by_cases sameRow : i = j
  rw [sameRow, Matrix.updateRow_self]
  rw [Matrix.updateRow_ne, Matrix.updateRow_self]
  exact sameRow

/-- Row `j` of matrix `M` will be the previous row `i` after swapping rows `i` and `j`. -/
@[simp]
lemma swapRow_eq_second (M : Matrix m n α) (i : m) (j : m) :
    swapRow M i j j = M i := by
  rw [swapRow, dupRow]
  by_cases sameRow : j = i
  rw [sameRow, Matrix.updateRow_self]
  rw [Matrix.updateRow_self]

/-- Some row `k` of matrix `M` will remain unchanged after swapping rows `i` and `j`. -/
@[simp]
lemma swapRow_other_rows_same (M : Matrix m n α) (i : m) (j : m) (k : m) (h1 : k ≠ i) (h2 : k ≠ j) :
    swapRow M i j k = M k := by
  rw [swapRow, dupRow]
  rw [Matrix.updateRow_ne, Matrix.updateRow_ne]
  repeat assumption

/-! ### swapRow has a row operations which inverts it -/

/-- Swapping rows `i` and `j` of matrix `M` twice will return the original matrix `M`. -/
@[simp]
theorem swapRow_involutive (M : Matrix m n α) (i : m) (j : m) :
    swapRow (swapRow M i j) i j = M := by
  rw [← Matrix.ext_iff]
  intro p q
  by_cases peqi : p = i
  rw [peqi, swapRow_eq_first, swapRow_eq_second]
  by_cases peqj : p = j
  rw [peqj, swapRow_eq_second, swapRow_eq_first]
  rw [swapRow_other_rows_same, swapRow_other_rows_same]
  repeat assumption

/-! ### swapRow is equivalent to a multiplication by the identity matrix -/

/-- Multiplying matrix `M` by the elementary matrix derived from swapping rows `i` and `j` of the
identity matrix is equivalent to swapping rows `i` and `j` of matrix `M`. -/
@[simp]
theorem swapRow_elem_mat_eq_swapRow [Fintype m] [DivisionRing α] (M : Matrix m m α) (i : m)
    (j : m) :
    (swapRow_elem_mat i j : Matrix m m α) * M = swapRow M i j := by
  rw [swapRow_elem_mat]
  ext p q
  by_cases peqi : p = i
  rw [peqi, swapRow_eq_first]
  rw [Matrix.mul_apply, swapRow_eq_first]
  simp_rw [Matrix.one_apply]
  simp
  by_cases peqj : p = j
  rw [peqj, swapRow_eq_second, Matrix.mul_apply, swapRow_eq_second]
  simp_rw [Matrix.one_apply]
  simp
  rw [swapRow_other_rows_same, Matrix.mul_apply, swapRow_other_rows_same]
  simp_rw [Matrix.one_apply]
  simp
  exact peqi
  exact peqj
  exact peqi
  exact peqj


/-! ### swapRow has a left inverse -/

/-- Multiplying the elementary matrix derived from swapping rows `i` and `j` of the identity matrix
by itself reverts it to the identity matrix. `swapRow_elem_mat` is it's own inverse. -/
theorem swapRow_elem_inv [Fintype m] [DivisionRing α] (i : m) (j : m) :
    (swapRow_elem_mat i j : Matrix m m α) * (swapRow_elem_mat i j : Matrix m m α)
    = (1 : Matrix m m α) := by
  rw [swapRow_elem_mat_eq_swapRow, swapRow_elem_mat, swapRow_involutive]

/-! ### extra -/

/-- Swapping rows `i` and `j` of matrix `M` is equivalent to swapping row `j` with row `i`. -/
lemma swapRow_comm (M : Matrix m n α) (i : m) (j : m) :
    swapRow M i j = swapRow M j i := by
  rw [← Matrix.ext_iff]
  intro p q
  by_cases peqi : p = i
  rw [peqi, swapRow_eq_second, swapRow_eq_first]
  by_cases peqj : p = j
  rw [peqj, swapRow_eq_first, swapRow_eq_second]
  rw [swapRow_other_rows_same, swapRow_other_rows_same]
  repeat assumption

end swapRow

section mulRow

/-! ### Declarations about `mulRow` -/

/-- Multiplies the `i`th row of matrix `M` by scalar `x`. -/
def mulRow [SMul R α] (M : Matrix m n α) (i : m) (x : R) : Matrix m n α :=
  updateRow M i (x • M i)

/-- Multiplies the `i`th row of identity matrix by scalar `x`, resulting in an elementary matrix -/
def mulRow_elem_mat [SMul R α] [One α] [Zero α] (i : m) (x : R) : Matrix m m α :=
  mulRow (1 : Matrix m m α) i x

/-! ### Basic properties of mulRow -/

/-- Row `i` of matrix `M` will be scaled by `x` after multiplying row `i` by scalar `x`. -/
@[simp]
lemma mulRow_eq_mul_row [SMul R α] (M : Matrix m n α) (i : m) (x : R) :
    mulRow M i x i = x • M i := by
  rw [mulRow, updateRow_self]

/-- Some row `j` of matrix `M` will remain unchanged after multiplying row `i` by scalar `x`. -/
@[simp]
lemma mulRow_other_rows_same [SMul R α] (M : Matrix m n α) (i : m) (j : m) (h1 : j ≠ i) (x : R) :
    mulRow M i x j = M j := by
  rw [mulRow, updateRow_ne]; exact h1

/-! ### mulRow has a row operations which inverts it -/

/-- Multiplying row `i` of matrix `M` by a non-zero scalar `x` and then by `x`'s multiplicative
inverse will return the original matrix `M`. -/
@[simp]
theorem mulRow_mulRow_inv_cancel_right [GroupWithZero R] [MulAction R α] (M : Matrix m n α) (i : m)
    (x : R) (hx : x ≠ 0) :
    mulRow (mulRow M i x) i (x⁻¹) = M := by
  unfold mulRow
  ext k l
  by_cases h : k = i
  · rw [h]
    repeat rw [updateRow_self]
    simp
    rw [smul_smul (x⁻¹) x (M i l)]
    rw [inv_mul_cancel₀]
    simp
    exact hx
  · repeat rw [updateRow_ne h]

/-- Multiplying row `i` of matrix `M` by a non-zero scalar `x`'s multiplicative inverse and then by
`x`' will return the original matrix `M`. -/
@[simp]
theorem mulRow_mulRow_inv_cancel_left [GroupWithZero R] [MulAction R α] (M : Matrix m n α) (i : m)
    (x : R) (hx : x ≠ 0) :
    mulRow (mulRow M i x⁻¹) i (x) = M := by
  unfold mulRow
  ext k l
  by_cases h : k = i
  · rw [h]
    repeat rw [updateRow_self]
    simp
    rw [smul_smul x (x⁻¹) (M i l)]
    rw [mul_inv_cancel₀]
    simp
    exact hx
  · repeat rw [updateRow_ne h]

/-! ### mulRow is equivalent to a multiplication by the identity matrix -/

/-- Multiplying matrix `M` by the elementary matrix derived from multiplying row `i` of the
identity matrix by scalar `x` is equivalent to multiplying row `i` of matrix `M` by scalar `x` -/
@[simp]
theorem mulRow_elem_mat_eq_mulRow [Fintype m] [DivisionRing α] [SMul R α] (M : Matrix m m α)
    (i : m) (x : R) :
    (mulRow_elem_mat i x) * M = mulRow M i x := by
  rw [mulRow_elem_mat]
  ext k l
  by_cases h : k = i
  · rw [h, mulRow_eq_mul_row]
    rw [mul_apply, mulRow_eq_mul_row]
    -- THIS NEXT SIMP IT TURNS INTO SCALAR MUL INSTEAD OF MUL
    simp
    simp_rw [one_apply]
    sorry
    -- need to figure out how to finish
  · rw [mulRow_other_rows_same]
    rw [mul_apply, mulRow_other_rows_same]
    simp_rw [one_apply]
    simp
    repeat exact h

-- /-- Multiplying matrix `M` by the elementary matrix derived from multiplying row `i` of the
-- identity matrix by scalar `x` is equivalent to multiplying row `i` of matrix `M` by scalar `x` -/
-- @[simp]
-- theorem mulRow_id_mul_mat_eq_mulRow [Fintype m] [Fintype n] (M : Matrix m n ℝ) (i : m) (x : ℝ) :
--     mulRow (1 : Matrix m m ℝ) i x * M = mulRow M i x := by
--   ext k l
--   by_cases h : k = i
--   · rw [h, mulRow_eq_mul_row]
--     rw [mul_apply, mulRow_eq_mul_row]
--     simp
--     simp_rw [one_apply]
--     simp
--   · rw [mulRow_other_rows_same]
--     rw [mul_apply, mulRow_other_rows_same]
--     simp_rw [one_apply]
--     simp
--     repeat exact h

-- there is a matrix that if multiplying by the elementary matrix you will get the identity matrix

/-! ### extra -/

/-- The value at row `i` and column `l` of matrix `M` will be 1 after multiplying row `i` by the
multiplicative inverse of the value located at row `i` and column `l`, which must be non-zero. -/
@[simp]
theorem mulRow_inv_cancel [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ}
    (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (l : Fin z) (h : M i l ≠ 0) :
    (mulRow M i (1/(M i l))) i l = 1 := by
  unfold mulRow
  simp
  rw [inv_mul_cancel₀]
  exact h

end mulRow

section addMulRow

/-! ### Declarations about `addMulRow` -/

/-- Adds the `j`th row of matrix `M` times scalar `x` to row `i`. -/
def addMulRow [SMul R α] [Add α] (M : Matrix m n α) (i : m) (j : m) (x : R): Matrix m n α :=
  updateRow M i (M i + x • M j)

/-! ### Basic properties of addMulRow -/

/-- Row `i` of matrix `M` will be the result of adding row `j` times scalar `x` to row the original
row `i` after adding row `j` times scalar `x` to row `i`. -/
@[simp]
lemma addMulRow_eq_add_mul_row [SMul R α] [Add α] (M : Matrix m n α) (i : m) (j : m) (x : R) :
    addMulRow M i j x i = M i + x • M j := by
  rw [addMulRow]
  by_cases h : i = j
  · rw [h, updateRow_self]
  · rw [updateRow_self]

/-- Some row `k`of matrix `M` will remain unchanged after adding row `j` times scalar `x` to
row `i`. -/
@[simp]
lemma addMulRow_other_rows_same [SMul R α] [Add α] (M : Matrix m n α) (i : m) (j : m) (k : m)
    (h1 : k ≠ i) (x : R) :
    addMulRow M i j x k = M k := by
  rw [addMulRow]
  rw [updateRow_ne h1]

/-! ### addMulRow has a row operations which inverts it -/

/-- Adding row `j` of matrix `M` times scalar `x` to row `i` and then adding row `j` times `-x` to
row `i` will return the original matrix `M`. -/
@[simp]
theorem addMulRow_addMulRow_neg_cancel [Ring R] [AddCommGroup α] [Module R α] (M : Matrix m n α)
    (i : m) (j : m) (h1 : j ≠ i) (x : R) :
    addMulRow (addMulRow M i j x) i j (-x) = M := by
  unfold addMulRow
  ext k l
  by_cases h : k = i
  · rw [h]
    repeat rw [updateRow_self]
    rw [updateRow_ne]
    simp
    exact h1
  · rw [updateRow_ne h]
    rw [updateRow_ne h]

/-! ### addMulRow is equivalent to a multiplication by the identity matrix -/

/-- Multiplying matrix `M` by the elementary matrix derived from adding row `j` of the identity
matrix times scalar `x` to row `i`of the identity matrix is equivalent to adding row `j` of matrix
`M` times scalar `x` to row `i` of matrix `M`. -/
@[simp]
theorem addMulRow_id_mul_eq_addMulRow [Fintype m] [Fintype n]
    (M : Matrix m n ℝ) (i : m) (j : m) (x : ℝ) :
    addMulRow (1 : Matrix m m ℝ) i j x * M = addMulRow M i j x := by
  ext k l
  by_cases h : k = i
  · rw [h, addMulRow_eq_add_mul_row]
    rw [mul_apply, addMulRow_eq_add_mul_row]
    simp
    simp_rw [one_apply]
    simp
    simp [add_mul]
    rw [Finset.sum_add_distrib]
    simp

  · rw [addMulRow_other_rows_same]
    rw [mul_apply, addMulRow_other_rows_same]
    simp_rw [one_apply]
    simp
    exact h
    exact h

/-! ### extra -/

-- k is the row where the value will become
/-- The value at row `i` and column `l` of matrix `M` will be 0 after adding row `j` times the
negative of the value at row `i` and column `l` divided by the value at row `j` and column `l`
to row `i`. -/
@[simp]
theorem addMulRow_inv_cancel [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ}
    (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin y) (l : Fin z) (h : M j l ≠ 0) :
    (addMulRow M i j (-(M i l)*(1/(M j l)))) i l = 0 := by
  unfold addMulRow
  simp
  rw [mul_assoc]
  rw [inv_mul_cancel₀]
  · simp
  · exact h

end addMulRow

end Matrix
