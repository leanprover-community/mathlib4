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

-- add summary

## Main definitions

- `swapRow`: A row is swaped with another row.
- `mulRow`: A row is multiplied by a non-zero constant, also known as scaling a row.
- `addMulRow`: A multiple of another row is added to the row.

## Main statements

-- add one that mentions the final theorem that all elementary matrices are invertible
-

## Implementation Notes



## References

<https://en.wikipedia.org/wiki/Elementary_matrix>

## Tags

matrix, elementary matrices, matrix operations, elementary row operations, linear algebra


-/

variable {m n α R : Type*}
-- m is used for rows
-- n is used for columns
-- α is for entries
-- R is used for scalar multiplication on matrices (should it be a different type?)

-- i, j, k, l are used as variable name for row : m
-- x is used as variable name for multiplication : R


open Matrix

namespace Matrix

variable [DecidableEq m]

section swapRow

-- Copies Row j to Row i, used in SwapRow

def dupRow (M : Matrix m n α) (i : m) (j : m) : Matrix m n α :=
  updateRow M i (M j)

-- Operation with swaps Row i and j
def swapRow (M : Matrix m n α) (i : m) (j : m) : Matrix m n α :=
  updateRow (dupRow M i j) j (M i)

-- TO BE CHANGED
-- -- If you swap Row i and j then Row i will be the previous Row j
-- lemma swapRowi [DecidableEq m](M : Matrix m n α) (i : m) (j : m)
--   : swapRow M i j i = M j := by
--   rw [swapRow, dupRow]
--   by_cases sameRow : i = j
--   rw [sameRow, Matrix.updateRow_self]
--   rw [Matrix.updateRow_ne, Matrix.updateRow_self]
--   exact sameRow

-- -- If you swap Row i and j then Row j will be the previous Row i
-- lemma swapRowj [DecidableEq m](M : Matrix m n α) (i : m) (j : m)
--   : swapRow M i j j = M i := by
--   rw [swapRow, dupRow]
--   by_cases sameRow : j = i
--   rw [sameRow, Matrix.updateRow_self]
--   rw [Matrix.updateRow_self]

-- --If you swap Rows i and j then all other rows stay the same
-- lemma swapRownotij [DecidableEq m](M : Matrix m n α) (i : m) (j : m) (p : m) (h1 : p ≠ i) (h2 : p ≠ j)
--   : swapRow M i j p = M p := by
--   rw [swapRow, dupRow]
--   rw [Matrix.updateRow_ne, Matrix.updateRow_ne]
--   repeat assumption

-- -- The order of the parameters in swapRow does not matter
-- lemma swapRowijEqji [DecidableEq m](M : Matrix m n α) (i : m) (j : m)
--   : swapRow M i j = swapRow M j i := by
--   rw [← Matrix.ext_iff]
--   intro p q
--   by_cases peqi : p = i
--   rw [peqi, swapRowj, swapRowi]
--   by_cases peqj : p = j
--   rw [peqj, swapRowi, swapRowj]
--   rw [swapRownotij, swapRownotij]
--   repeat assumption

-- -- Calling swapRow twice gives you the original matrix back
-- theorem swapSwapEq [DecidableEq m] (M : Matrix m n α) (i : m) (j : m)
--   : swapRow (swapRow M i j) i j = M := by
--   rw [← Matrix.ext_iff]
--   intro p q
--   by_cases peqi : p = i
--   rw [peqi, swapRowi, swapRowj]
--   by_cases peqj : p = j
--   rw [peqj, swapRowj, swapRowi]
--   rw [swapRownotij, swapRownotij]
--   repeat assumption

-- -- elemMatSwap i j is the elementary matrix formed by swapping rows i and j in the identity
-- def elemMatSwap [DecidableEq n] [One α] [Zero α] (i : n) (j : n) : Matrix n n α :=
--   swapRow (1 : Matrix n n α) i j

-- --   Multiplying elemMatSwap i j by M is the same as swapping rows i and j of M
-- theorem swapMatEqSwap [DecidableEq n]
--   [Fintype n] [Fintype m]
--   (M : Matrix n m γ) (i : n) (j : n)
--   : (elemMatSwap i j : Matrix n n γ) * M = swapRow M i j := by
--   rw [elemMatSwap]
--   ext p q
--   by_cases peqi : p = i
--   rw [peqi, swapRowi]
--   rw [Matrix.mul_apply, swapRowi]
--   simp_rw [Matrix.one_apply]
--   simp
--   by_cases peqj : p = j
--   rw [peqj, swapRowj, Matrix.mul_apply, swapRowj]
--   simp_rw [Matrix.one_apply]
--   simp
--   rw [swapRownotij, Matrix.mul_apply, swapRownotij]
--   simp_rw [Matrix.one_apply]
--   simp
--   exact peqi
--   exact peqj
--   exact peqi
--   exact peqj

-- -- THE FOLLOWING 3 DO NOT EXIST FOR THE OTHER ONES
-- -- elemMatSwap is its own inverse
-- theorem swapMatOwnInv [DecidableEq n]
--   [Fintype n]
--   (i : n) (j : n)
--   : (elemMatSwap i j : Matrix n n γ) * (elemMatSwap i j : Matrix n n γ) = (1 : Matrix n n γ) := by
--   rw [swapMatEqSwap, elemMatSwap, swapSwapEq]

-- -- if M * N = P
-- --   then this will still be true if the rows of M and P are swapped consistently
-- -- This theorem will be used to show that solutions are preserved by swapping rows
-- -- When we use it, N and P will only have one column
-- theorem swapImpliesSwapMat [DecidableEq m]
--   [Fintype n] [Fintype m] [Fintype p]
--   (M : Matrix m n γ) (N : Matrix n p γ) (P : Matrix m p γ) (i : m) (j : m) (h : M * N = P)
--   : swapRow M i j * N = swapRow P i j := by
--   rw [← swapMatEqSwap, ← swapMatEqSwap, Matrix.mul_assoc, h]

-- -- This is the companion to the above theorem
-- -- The above theorem shows that all are still there after the row operation
-- -- The below theorem shows that no new solutions are added
-- theorem swapMatImpliesSwap [DecidableEq m]
--   [Fintype m] [Fintype n] [Fintype p]
--   (M : Matre m] [Fintype n] [Fintype p]
--   (M : Matrix m n γ) (N : Matrix n p γ) (P : Matrix m p γ) (i : m) (j : m)
--   (h : swapRow M i j * N = swapRow P i j)
--   : M * N = P := by
--   rw [← swapMatEqSwapOld P i j] at h
--   rw [← swapSwapEq M i j]
--   rw [← swapMatEqSwapOld]
--   rw [Matrix.mul_assoc, h]
--   rw [← Matrix.mul_assoc, swapMatOwnInvOld]
--   simpix m n γ) (N : Matrix n p γ) (P : Matrix m p γ) (i : m) (j : m)
--   (h : swapRow M i j * N = swapRow P i j)
--   : M * N = P := by
--   rw [← swapMatEqSwap P i j] at h
--   rw [← swapSwapEq M i j]
--   rw [← swapMatEqSwap]
--   rw [Matrix.mul_assoc, h]
--   rw [← Matrix.mul_assoc, swapMatOwnInv]
--   simp

end swapRow

section mulRow

-- Operation which multiplies x by Row i
def mulRow [SMul R α] (M : Matrix m n α) (i : m) (x : R) : Matrix m n α :=
  updateRow M i (x • M i)

-- If you multiply Row i by x then Row i will be the it will change to that
@[simp]
lemma mulRow_eq_mul_row [SMul R α] (M : Matrix m n α) (i : m) (x : R) :
    mulRow M i x i = x • M i := by
  rw [mulRow, updateRow_self]

-- If you multiply Row i by x then all other rows stay the same
@[simp]
lemma mulRow_other_rows_same [SMul R α] (M : Matrix m n α) (i : m) (j : m) (h1 : j ≠ i) (x : R) :
    mulRow M i x j = M j := by
  rw [mulRow, updateRow_ne]; exact h1

--If you multiply Row i by x and then by 1/x you will get the original (right inverse)
@[simp]
theorem mulRow_mulRow_inv_cancel [GroupWithZero R] [MulAction R α] (M : Matrix m n α) (i : m)
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

-- Do the same as above but for left inverse
@[simp]
theorem mulRow_mulRow_inv_cancel_left [GroupWithZero R] [MulAction R α] (M : Matrix m n α) (i : m)
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

-- CHANGE VARIABLE NAMES MAYBE (j is a column here i think?)
@[simp]
theorem mulRow_inv_cancel [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ}
    (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (h : M i j ≠ 0) :
    (mulRow M i (1/(M i j))) i j = 1 := by
  unfold mulRow
  simp
  rw [inv_mul_cancel₀]
  exact h

-- Let Eix by the elementary matrix formed by multiplying Row i of the identity matrix by x
-- Here we show that multiplying Eix by M is the same as multiplying Row i of M by x
@[simp]
theorem mulRow_id_mul_mat_eq_mulRow_mat [Fintype m] [Fintype n] (M : Matrix m n ℝ)
    (i : m) (x : ℝ) :
    mulRow (1 : Matrix m m ℝ) i x * M = mulRow M i x := by
  ext k l
  by_cases h : k = i
  · rw [h, mulRow_eq_mul_row]
    rw [mul_apply, mulRow_eq_mul_row]
    simp
    simp_rw [one_apply]
    simp
  · rw [mulRow_other_rows_same]
    rw [mul_apply, mulRow_other_rows_same]
    simp_rw [one_apply]
    simp
    repeat exact h
    --exact h

end mulRow

section addMulRow

-- Operation which add x times Row j to Row i
def addMulRow [SMul R α] [Add α] (M : Matrix m n α) (i : m) (j : m) (x : R): Matrix m n α :=
  updateRow M i (M i + x • M j)

-- If you add a multiple of Row j into Row i, then it will be the original i plus the multiple of Row j
@[simp]
lemma addMulRow_eq_add_mul_row [SMul R α] [Add α] (M : Matrix m n α) (i : m) (j : m) (x : R) :
    addMulRow M i j x i = M i + x • M j := by
  rw [addMulRow]
  by_cases h : i = j
  · rw [h, updateRow_self]
  · rw [updateRow_self]

-- If you add a multiple of Roa j into Row i, then all other rows will remain the same
@[simp]
lemma addMulRow_other_rows_same [SMul R α] [Add α] (M : Matrix m n α) (i : m) (j : m) (k : m)
    (h1 : k ≠ i) (x : R) :
    addMulRow M i j x k = M k := by
  rw [addMulRow]
  rw [updateRow_ne h1]

-- If you add a multiple of Row j into Row i, then substract the same multiple of Row j from Row will get the original matrix back
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

-- Let Eijx by the elementary matrix formed by adding a multiple of Row j to Row i of the identity matrix
-- Here we show that multiplying Eijx by M is the same as adding a multiple of Row j into Row i of M
@[simp]
theorem addMulRow_id_mul_eq_addMulRow_mat [Fintype m] [Fintype n]
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

-- k is the row where the value will become
@[simp]
theorem addMulRow_inv_cancel [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ}
    (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (k : Fin y) (h : M i j ≠ 0) :
    (addMulRow M k i (-(M k j)*(1/(M i j)))) k j = 0 := by
  unfold addMulRow
  simp
  rw [mul_assoc]
  rw [inv_mul_cancel₀]
  · simp
  · exact h

end addMulRow

end Matrix

-- -- If you replace a row by the same row, the matrix is unchanged
-- lemma replaceSame [DecidableEq m](M : Matrix m n α) (i : m) : Matrix.updateRow M i (M i) = M := by
--   rw [← Matrix.ext_iff]
--   intros p q
--   by_cases peqi : p = i
--   rw [peqi, Matrix.updateRow_self]
--   rw [Matrix.updateRow_ne]
--   exact peqi
