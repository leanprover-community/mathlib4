/-
Copyright (c) 2024 Mark Santa Clara Munro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Santa Clara Munro, Christopher Lynch
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.RowCol
import Mathlib.Data.Matrix.ElementaryRowOperations

/-!
# Gaussian Elimination



## Main definitions



## Main statements



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

-- /-- -/
-- theorem addMulRowToZero [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ}
--     (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (k : Fin y) (h : M i j ≠ 0) :
--     (addMulRow M k i (-(M k j)*(1/(M i j)))) k j = 0 := by
--   unfold addMulRow
--   simp
--   rw [mul_assoc]
--   rw [inv_mul_cancel]
--   · simp
--   · exact h

/-- Adding row `j` of matrix `M` times scalar `-(M i l) * (1 / (M j l)` to row `i` will make the
element at row `i` and column `l` be `0`. `M i l` stands for the element at row `i` and column `l`,
and `M j l` stands for the element at row `j` and column `l`. -/
theorem addMulRowToZero [DivisionRing α] (M : Matrix m n α) (i : m) (j : m) (l : n)
    (h : M j l ≠ 0) :
    (addMulRow M i j (-(M i l) * (1 / (M j l)))) i l = 0 := by
  unfold addMulRow
  simp only [one_div, neg_mul, neg_smul, updateRow_self, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [mul_assoc]
  rw [inv_mul_cancel₀]
  · simp only [mul_one, add_neg_cancel]
  · exact h

/-- -/
theorem lessSucc {y : ℕ} (i : Fin y) (hi : (i + 1: ℕ) ≠ y) : i + 1 < y := by
  omega

/-- -/
theorem morePrev {y : ℕ} (i : Fin y) : i - 1 < y := by
  omega

-- returns row index between 2 elements
-- /-- Returns the row index of the highest value between the element at row `i` and column `l` of
-- matrix `M` and the element at row `j` and column `l`. -/
-- def maxMatCol [LinearOrder α] [AddGroup α] {y : ℕ} {z : ℕ} (M : Matrix (Fin y) (Fin z) α)
--     (i : Fin y) (k : Fin y) (j : Fin z) [Decidable (|M i j| ≥ |M k j|)] :
--   Fin y := if |M i j| ≥ |M k j| then i else k

/-- Returns the row index of the highest value between the element at row `i` and column `l` of
matrix `M` and the element at row `j` and column `l`. -/
def maxMatCol [Lattice α] [AddGroup α] (M : Matrix m n α)
    (i : m) (j : m) (l : n) [Decidable (|M i l| ≥ |M j l|)] :=
    if |M i l| ≥ |M j l| then i else j

/-- Returns the row index of the highest value between the element at row `i` and column `l` of
matrix `M` and the element at row `j` and column `l`. -/
def maxMatCol1 [LinearOrder α] [AddGroup α] (M : Matrix m n α)
    (i : m) (j : m) (l : n) :=
    if |M i l| ≥ |M j l| then i else j

-- /-- The row index of the highest value between the element at row `i` and column `l` of matrix `M`
-- and the element at row `j` and column `l` is either row `i` or row `j`. -/
-- theorem maxMatColEither [LinearOrder α] [AddGroup α] {y : ℕ} {z : ℕ} (M : Matrix (Fin y) (Fin z) α)
--     (i : Fin y) (k : Fin y) (j : Fin z) [Decidable (|M i j| ≥ |M k j|)] :
--     maxMatCol M i k j = i ∨ maxMatCol M i k j = k := by
--   unfold maxMatCol
--   split
--   simp
--   simp

/-- The row index of the highest value between the element at row `i` and column `l` of matrix `M`
and the element at row `j` and column `l` is either row `i` or row `j`. -/
theorem maxMatColEither [LinearOrder α] [AddGroup α] (M : Matrix m n α)
    (i : m) (j : m) (l : n) :
    maxMatCol M i j l = i ∨ maxMatCol M i j l = j := by
  unfold maxMatCol
  split
  · simp
  · simp

-- /-- The element at column `l` of matrix `M` and the row index of the highest value between the
-- element at row `i` and column `l` and the element at row `j` and column `l` is greater than or
-- equal to the element at row `i` and column `l`. -/
-- theorem maxMatColGreaterLeft [LinearOrder α] [AddGroup α] {y : ℕ} {z : ℕ}
--     (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (k : Fin y) (j : Fin z)
--     [Decidable (|M i j| ≥ |M k j|)] : |M (maxMatCol M i k j) j| ≥ |M i j| := by
--   unfold maxMatCol
--   split_ifs with h
--   · simp
--   · rw [not_le] at h
--     exact le_of_lt h

/-- The element at column `l` of matrix `M` and the row index of the highest value between the
element at row `i` and column `l` and the element at row `j` and column `l` is greater than or
equal to the element at row `i` and column `l`. -/
theorem maxMatColGreaterLeft [LinearOrder α] [AddGroup α] (M : Matrix m n α) (i : m) (j : m)
    (l : n) :
    |M (maxMatCol M i j l) l| ≥ |M i l| := by
  unfold maxMatCol
  split_ifs with h
  · simp
  · rw [not_le] at h
    exact le_of_lt h

-- /-- The element at column `l` of matrix `M` and the row index of the highest value between the
-- element at row `i` and column `l` and the element at row `j` and column `l` is greater than or
-- equal to the element at row `j` and column `l`. -/
-- theorem maxMatColGreaterRight [LinearOrder α] [AddGroup α] {y : ℕ} {z : ℕ}
--     (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (k : Fin y) (j : Fin z)
--     [Decidable (|M i j| ≥ |M k j|)] : |M (maxMatCol M i k j) j| ≥ |M k j| := by
--   unfold maxMatCol
--   split_ifs with h
--   · exact h
--   · simp

/-- The element at column `l` of matrix `M` and the row index of the highest value between the
element at row `i` and column `l` and the element at row `j` and column `l` is greater than or
equal to the element at row `j` and column `l`. -/
theorem maxMatColGreaterRight [LinearOrder α] [AddGroup α] (M : Matrix m n α) (i : m) (j : m)
    (l : n) :
    |M (maxMatCol M i j l) l| ≥ |M j l| := by
  unfold maxMatCol
  split_ifs with h
  · exact h
  · simp

-- returns row index with the max value of the column
/-- -/
def maxColVal_RowPos [LinearOrder α][AddGroup α] {y : ℕ} {z : ℕ} (M : Matrix (Fin y) (Fin z) α)
  (i : Fin y) (j : Fin z) [∀ (x : α)  (y : α), Decidable (|x| ≥ |y|)] :
  Fin y := if h1 : i + 1 = y then i
     else
     let isucc := (⟨i+1,lessSucc i h1⟩ : Fin y)
     let k := maxColVal_RowPos M isucc j
     maxMatCol M i k j
  termination_by y - i

/-- -/
theorem maxColVal_RowPos_Max [LinearOrder α] [AddGroup α] {y : ℕ} {z : ℕ}
    (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z)
    [∀ (x : α)  (y : α), Decidable (|x| ≥ |y|)] : maxColVal_RowPos M i j ≥ i := by
  unfold maxColVal_RowPos
  --intro i
  split_ifs with h1
  exact Preorder.le_refl i
  --rw [maxColVal_RowPos_Max]
  unfold_let
  unfold maxMatCol
  split_ifs with h2
  exact Preorder.le_refl i
  let isucc := (⟨i+1,lessSucc i h1⟩ : Fin y)
  have h3 : isucc ≤ maxColVal_RowPos M isucc j
    := by apply maxColVal_RowPos_Max
  have h4 : i ≤ isucc
    := by unfold_let ; rw [Fin.mk_le_mk] ; simp
  apply Preorder.le_trans i isucc (maxColVal_RowPos M isucc j)
  exact h4
  exact h3
termination_by y - i

-- theorem maxColVal_RowPos_Max2
--   [LinearOrder α] [AddGroup α]
--   {y : ℕ} {z : ℕ}
--   (M : Matrix (Fin y) (Fin z) α)
--   (i : Fin y)
--   (j : Fin z)
--   [∀ (x : α)  (y : α), Decidable (|x| ≥ |y|)]
--   : maxColVal_RowPos M i j ≥ i := by
--   unfold maxColVal_RowPos
--   split_ifs with h1
--   exact Preorder.le_refl i
--   --unfold_let
--   let isucc := (⟨i+1,lessSucc i h1⟩ : Fin y)
--   let k := maxColVal_RowPos M isucc j
--   cases' (maxMatColEither M i k j) with h1 h2
--   rw [h1]
--   rw [h2]
--   have h3 : isucc ≤ maxColVal_RowPos M isucc j
--     := by apply maxColVal_RowPos_Max2
--   have h4 : i ≤ isucc
--     := by unfold_let ; rw [Fin.mk_le_mk] ; simp
--   apply Preorder.le_trans i isucc k
--   exact h4
--   exact h3
-- termination_by y - i

-- p stands for the row of the pivot, i stands for below p row, j stands for specified column
-- turns all numbers on column j below p into 0
/-- -/
def turnBelowIntoZero [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ}
    (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (p : Fin y) : Matrix (Fin y) (Fin z) α :=
  if h1 : i + 1 = y then addMulRow M i p (-(M i j)*(1/(M p j)))
  else
    let isucc := (⟨i+1, lessSucc i h1⟩ : Fin y)
    if M i j = 0 then turnBelowIntoZero M isucc j p
    else
      let M' := addMulRow M i p (-(M i j)*(1/(M p j)))
      turnBelowIntoZero M' isucc j p
termination_by y - i

/-- -/
theorem turnBelowIntoZeroProof [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ}
    (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (p : Fin y) (h1 : i = (p : ℕ) + 1)
    (h2 : M p j ≠ 0) :
    (turnBelowIntoZero M i j p) i j = 0 := by
  unfold turnBelowIntoZero
  split_ifs with h3
  · apply addMulRowToZero
    exact h2
  · let isucc := (⟨i+1,lessSucc i h1⟩ : Fin y)
    unfold_let
    unfold turnBelowIntoZero

    · done
    · done
  · done

/-- -/
theorem maxColVal_RowPos_Max2 [LinearOrder α] [AddGroup α] {y : ℕ} {z : ℕ}
    (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z)
    [∀ (x : α)  (y : α), Decidable (|x| ≥ |y|)] :
    maxColVal_RowPos M i j ≥ i := by
  unfold maxColVal_RowPos
  split_ifs with h1
  · exact Preorder.le_refl i
  · let isucc := (⟨i+1,lessSucc i h1⟩ : Fin y)
    let k := maxColVal_RowPos M isucc j
    cases' (maxMatColEither M i k j) with h1 h2
    · rw [h1]
    · rw [h2]
      have h3 : isucc ≤ maxColVal_RowPos M isucc j
        := by apply maxColVal_RowPos_Max2
      have h4 : i ≤ isucc
        := by unfold_let ; rw [Fin.mk_le_mk] ; simp
      apply Preorder.le_trans i isucc k
      exact h4
      exact h3
      termination_by y - i

-- theorem turnBelowIntoZeroProof [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ}
--   (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (p : Fin y) :
--   ∀ (k : Fin y), k > i → (turnBelowIntoZero M i j p) k j = 0 := by
--   induction y - i
--   · intro h hk
--     unfold turnBelowIntoZero
--     unfold_let
--     split_ifs with h1
--     ·

--     · done
--   ·

-- p for the row of the pivot, i stands for row below p, j for specified column
-- turns all numbers on column j below  p into 0
/-- -/
def turnAboveIntoZero [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ}
    (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (p : Fin y) :
    Matrix (Fin y) (Fin z) α := if h: (i : ℕ) = 0 then addMulRow M i p (-(M i j)*(1/(M p j)))
  else
    let iprev := (⟨i-1, morePrev i⟩ : Fin y)
    have : iprev < i := by
      unfold_let iprev
      rw [Fin.mk_lt_mk]
      omega
    if M i j = 0 then turnAboveIntoZero M iprev j p
    else
      let M' := addMulRow M i p (-(M i j)*(1/(M p j)))
      turnAboveIntoZero M' iprev j p
termination_by (i : ℕ)

#eval turnBelowIntoZero (!![1,1,2;1,2,1;2,1,1] : Matrix _ _ ℚ) 1 0 0
#eval turnBelowIntoZero (!![1,1,2,1;1,2,1,1;2,1,1,1;1,1,1,2] : Matrix _ _ ℚ) 1 0 0

#eval turnAboveIntoZero (!![1,1,2;1,2,1;2,1,1] : Matrix _ _ ℚ) 0 2 1
#eval turnAboveIntoZero (!![1,1,2,1;1,2,1,1;2,1,1,1;1,1,1,2] : Matrix _ _ ℚ) 2 3 3

-- does not turn pivots into 1s
/-- -/
def gaussForward [DecidableEq α] [DivisionRing α] [LinearOrder α] {y : ℕ} {z : ℕ}
    (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z)
    [∀ (x : α) (y : α), Decidable (|x| ≥ |y|)] :
    Matrix (Fin y) (Fin z) α :=
  if h1: i + 1 = y then M
  else
    let isucc := (⟨i+1,lessSucc i h1⟩ : Fin y)
    if h2 : j + 1 = z then M
    else
      let jsucc := (⟨j+1,lessSucc j h2⟩ : Fin z)
      let k := maxColVal_RowPos M i j
      if M k j = 0 then gaussForward M i jsucc
      else
        let M' := swapRow M i k
        let M'' := turnBelowIntoZero M' isucc j i
        gaussForward M'' isucc jsucc
termination_by (y - i) + (z - j)

#eval gaussForward (!![1,1,2;1,2,1;2,1,1] : Matrix _ _ ℚ) 0 0
#eval gaussForward (!![1,1,2,1;1,2,1,1;2,1,1,1;1,1,1,2] : Matrix _ _ ℚ) 0 0


-- includes turning pivots into 1s
/-- -/
def gaussForwardPivot [DecidableEq α] [DivisionRing α] [LinearOrder α] {y : ℕ} {z : ℕ}
    (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z)
    [∀ (x : α) (y : α), Decidable (|x| ≥ |y|)] :
    Matrix (Fin y) (Fin z) α :=
  if h1: i + 1 = y then M
  else
    let isucc := (⟨i+1,lessSucc i h1⟩ : Fin y)
    if h2 : j + 1 = z then M
    else
      let jsucc := (⟨j+1,lessSucc j h2⟩ : Fin z)
      let k := maxColVal_RowPos M i j
      if M k j = 0 then gaussForwardPivot M i jsucc
      else
        let M' := swapRow M i k
        let M'' := mulRow M' i (1/(M' i j))
        let M''' := turnBelowIntoZero M'' isucc j i
        gaussForwardPivot M''' isucc jsucc
termination_by (y - i) + (z - j)

#eval gaussForwardPivot (!![1,1,2;1,2,1;2,1,1] : Matrix _ _ ℚ) 0 0
#eval gaussForwardPivot (!![1,1,2,1;1,2,1,1;2,1,1,1;1,1,1,2] : Matrix _ _ ℚ) 0 0


-- full gaussian elimination
/-- -/
def gauss [DecidableEq α] [DivisionRing α] [LinearOrder α] {y : ℕ} {z : ℕ}
    (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z)
    [∀ (x : α) (y : α), Decidable (|x| ≥ |y|)] :
    Matrix (Fin y) (Fin z) α :=
  let iprev := (⟨i-1, morePrev i⟩ : Fin y)
  -- if at the end row, then make pivot into 0 and turn everything above into 0
  if h1: i + 1 = y then
  let Mi := mulRow M i (1/(M i j))
  turnAboveIntoZero Mi iprev j i
  else
    let isucc := (⟨i+1,lessSucc i h1⟩ : Fin y)
    -- if at the last column, then return
    if h2 : j + 1 = z then M
    else
      let jsucc := (⟨j+1,lessSucc j h2⟩ : Fin z)
      -- k is the row of the max abs value in column
      let k := maxColVal_RowPos M i j
      -- if the max value is zero, then skip to next column
      if M k j = 0 then gauss M i jsucc
      else
        let M' := swapRow M i k
        let M'' := mulRow M' i (1/(M' i j))
        let M''' := turnBelowIntoZero M'' isucc j i
        -- if it is the first row, can't do turnAboveIntoZero
        if (i : ℕ) = 0 then gauss M''' isucc jsucc
        else
          let M'''' := turnAboveIntoZero M''' iprev j i
          gauss M'''' isucc jsucc
termination_by (y - i) + (z - j)

#eval gauss (!![1,1,2;1,2,1;2,1,1] : Matrix _ _ ℚ) 0 0
#eval gauss (!![1,1,2,1;1,2,1,1;2,1,1,1;1,1,1,2] : Matrix _ _ ℚ) 0 0




-- old gauss (index ahead)

-- -- i stands for current row, j stands for specified column, y stands for the last row + 1, p stands for the row of the pivot
-- -- turns all numbers on column j below row i or p into 0
-- def turnBelowIntoZero [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ} (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (p : Fin y)
--   : Matrix (Fin y) (Fin z) α :=
--   if h1 : i + 1 = y then M
--   else
--     let isucc := (⟨i+1, lessSucc i h1⟩ : Fin y)
--     if M isucc j = 0 then turnBelowIntoZero M isucc j p
--     else
--       let M' := addMulRow M isucc p (-(M isucc j)*(1/(M p j)))
--       turnBelowIntoZero M' isucc j p
-- termination_by y - i

-- -- i stands for current row, j for specified column, p for the row of the pivot
-- -- turns all numbers on column j below row i or p into 0
-- def turnAboveIntoZero [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ} (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (p : Fin y)
--   : Matrix (Fin y) (Fin z) α :=
--   if h:(i : ℕ) = 0 then M
--   else
--     let iprev := (⟨i-1, morePrev i⟩ : Fin y)
--     have : iprev < i := by
--       unfold_let iprev
--       rw [Fin.mk_lt_mk]
--       omega
--     if M iprev j = 0 then turnAboveIntoZero M iprev j p
--     else
--       let M' := addMulRow M iprev p (-(M iprev j)*(1/(M p j)))
--       turnAboveIntoZero M' iprev j p
-- termination_by (i : ℕ)

-- -- does not turn pivots into 1s
-- def gaussForward
-- [DecidableEq α] [DivisionRing α] [LinearOrder α]
-- {y : ℕ} {z : ℕ} (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z)
-- [∀ (x : α) (y : α), Decidable (|x| ≥ |y|)]
--   : Matrix (Fin y) (Fin z) α :=
--   if h1: i + 1 = y then M
--   else
--     let isucc := (⟨i+1,lessSucc i h1⟩ : Fin y)
--     if h2 : j + 1 = z then M
--     else
--       let jsucc := (⟨j+1,lessSucc j h2⟩ : Fin z)
--       let k := maxColVal_RowPos M i j
--       if M k j = 0 then gaussForward M i jsucc
--       else
--         let M' := swapRow M i k
--         let M'' := turnBelowIntoZero M' i j i
--         gaussForward M'' isucc jsucc
-- termination_by (y - i) + (z - j)

-- -- #eval gaussForward (!![1,1,2;1,2,1;2,1,1] : Matrix _ _ ℚ) 0 0
-- -- #eval gaussForward (!![1,1,2,1;1,2,1,1;2,1,1,1;1,1,1,2] : Matrix _ _ ℚ) 1 1

-- -- includes turning pivots into 1s
-- def gaussForwardPivot
-- [DecidableEq α] [DivisionRing α] [LinearOrder α]
-- {y : ℕ} {z : ℕ} (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z)
-- [∀ (x : α) (y : α), Decidable (|x| ≥ |y|)]
--   : Matrix (Fin y) (Fin z) α :=
--   if h1: i + 1 = y then M
--   else
--     let isucc := (⟨i+1,lessSucc i h1⟩ : Fin y)
--     if h2 : j + 1 = z then M
--     else
--       let jsucc := (⟨j+1,lessSucc j h2⟩ : Fin z)
--       let k := maxColVal_RowPos M i j
--       if M k j = 0 then gaussForwardPivot M i jsucc
--       else
--         let M' := swapRow M i k
--         let M'' := mulRow M' i (1/(M' i j))
--         let M''' := turnBelowIntoZero M'' i j i
--         gaussForwardPivot M''' isucc jsucc
-- termination_by (y - i) + (z - j)

-- -- #eval gaussForwardPivot (!![1,1,2;1,2,1;2,1,1] : Matrix _ _ ℚ) 0 0
-- -- #eval gaussForwardPivot (!![1,1,2,1;1,2,1,1;2,1,1,1;1,1,1,2] : Matrix _ _ ℚ) 1 1

-- -- full gaussian elimination
-- def gauss
-- [DecidableEq α] [DivisionRing α] [LinearOrder α]
-- {y : ℕ} {z : ℕ} (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z)
-- [∀ (x : α) (y : α), Decidable (|x| ≥ |y|)]
--   : Matrix (Fin y) (Fin z) α :=
--   if h1: i + 1 = y then
--   let Mi := mulRow M i (1/(M i j))
--   turnAboveIntoZero Mi i j i
--   else
--     let isucc := (⟨i+1,lessSucc i h1⟩ : Fin y)
--     if h2 : j + 1 = z then M
--     else
--       let jsucc := (⟨j+1,lessSucc j h2⟩ : Fin z)
--       let k := maxColVal_RowPos M i j
--       if M k j = 0 then gauss M i jsucc
--       else
--         let M' := swapRow M i k
--         let M'' := mulRow M' i (1/(M' i j))
--         let M''' := turnBelowIntoZero M'' i j i
--         let M'''' := turnAboveIntoZero M''' i j i
--         gauss M'''' isucc jsucc
-- termination_by (y - i) + (z - j)

-- -- #eval gauss (!![1,1,2;1,2,1;2,1,1] : Matrix _ _ ℚ) 0 0
-- -- #eval gauss (!![1,1,2,1;1,2,1,1;2,1,1,1;1,1,1,2] : Matrix _ _ ℚ) 0 0





-- Ignore Below


-- def gauss M i j
-- -- if the current row is the last one return M (y is the row after the last one (remember index 0))
-- if h1 : i + 1 = y then M
-- -- if the current column is the last one return M (can happen when there is a column without a pivot)
-- else if h2 : j + 1 = z then M
--   -- k is actually the row with the max value, maxCol must look only at rows i and under
--   let k : maxCol M i j
--     -- this means that there is a non-zero value in that column
--     if M j k ≠ 0
--       -- makes the pivot have the largest value (have to check if it is now row i or k, and might need to use let)
--       swapRow M i k
--       -- i or k depends on the thing above
--       let M' turnBelowIntoZero M (i or k) j (i or k)
--       -- recursive call to next potential pivot
--       gauss M' isucc jsucc
--     -- if M j k is 0, then move to the next column
--     else gauss M i jsucc

--gauss M i j
-- if i = m
--   M
-- k = maxcol M i j
-- if M i k ≠ 0
--  swap M i k
--  turnBelowIntoZero
--  gauss M (i+1) (j+1)
-- else
--  gauss M i (j + 1)

-- def maxMatRow
--   [LE α]
--   {y : ℕ} {z : ℕ} (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (k : Fin z)
--   [Decidable (M i j ≥ M i k)]
--   : Fin z
--   := if M i j ≥ M i k then j else k

-- def maxRowVal_ColPos
--   [LE α]
--   {y : ℕ} {z : ℕ}
--   (M : Matrix (Fin y) (Fin z) α)
--   (i : Fin y) (j : Fin z)
--   [∀ (x : α)  (y : α), Decidable (x ≥ y)]
--   : Fin z
--   := if h1 : j + 1 = z then j
--      else
--      let jsucc := (⟨j+1,lessSucc j h1⟩ : Fin z)
--      let k := maxRowVal_ColPos M i jsucc
--      maxMatRow M i j k
--   termination_by z - j






-- theorem lessSucc {z : ℕ} (i:Fin z) (hi : (i + 1: ℕ) ≠ z) : i + 1 < z := by
--   omega

-- -- i stands for current row, j stands for specified column, z stands for the last row + 1, p stands for the row of the pivot
-- -- turns all numbers on column j below row i or p into 0
-- def turnBelowIntoZero [DecidableEq α] [DivisionRing α] {z : ℕ} (M : Matrix (Fin z) (Fin z) α) (i : Fin z) (j : Fin z) (p : Fin z)
--   : Matrix (Fin z) (Fin z) α :=
--   -- if the current row is the last row, then return matrix
--   if h1 : i + 1 = z then M
--   -- if the value of the position below is 0, move onto the next one below
--   else
--   let isucc := (⟨i+1,lessSucc i h1⟩ : Fin z)
--   if M isucc j = 0 then turnBelowIntoZero M isucc j p
--   -- if it is not 0, then make it into 0 and move on to the next one below with the changed matrix
--   else
--     let M' := addMulRow M isucc p (-(M isucc j)/(M p j))
--     turnBelowIntoZero M' isucc j p
-- termination_by z - i

-- #eval turnBelowIntoZero (!![1,7,1;8,54,2;7,0,9] : Matrix _ _ ℚ) 0 0 0
-- #eval turnBelowIntoZero (!![1,7,1;0,-2,-6;0,-49,2] : Matrix _ _ ℚ) 1 1 1



-- theorem lessSucc (i : ℕ) (z : ℕ) (h1 : i < z) (h2 : i ≠ z - 1): i + 1 < z := by
--   omega

-- -- i stands for current row, j stands for specified column, z stands for the last row + 1, p stands for the row of the pivot
-- -- turns all numbers on column j below row i or p into 0
--   def turnBelowIntoZero [GroupWithZero α] [DecidableEq α] [Add α] [Neg α] (M : Matrix ℕ ℕ α) (i : ℕ) (j : ℕ) (z : ℕ) (p : ℕ) (h : i < z)
--   : Matrix ℕ ℕ α :=
--   -- if the current row is the last row, then return matrix
--   if h1 : i = (z - 1) then M
--   -- if the value of the position below is 0, move onto the next one below
--   else if M (i + 1) j = 0 then turnBelowIntoZero M (i + 1) j z p (lessSucc i z h h1)
--   -- if it is not 0, then make it into 0 and move on to the next one below with the changed matrix
--   else
--     let M' := addMulRow M (i + 1) p (-(M (i+1) j)/(M p j))
--     turnBelowIntoZero M' (i + 1) j z p (lessSucc i z h h1)

-- -- def turnBelowIntoZero [GroupWithZero ℝ] [DecidableEq ℝ] [Add ℝ] [SMul ℝ ℝ] (M : Matrix ℕ ℕ ℝ) (i : ℕ) (j : ℕ) (z : ℕ) (p : ℕ) (h : i < z)
-- -- : Matrix ℕ ℕ ℝ :=
-- --   -- if the number right below the indexed position is zero, then recall the function
-- --   if h1 : i = (z - 1) then M
-- --   else if M (i + 1) j = 0 then turnBelowIntoZero M (i + 1) j z p (lessSucc i z h h1)
-- --   else
-- --     let M' := addMulRow M (i + 1) p (-(M (i+1) j)/(M p j))
-- --     turnBelowIntoZero M' (i + 1) j z p (lessSucc i z h h1)

-- -- #eval turnBelowIntoZero (!![1,2,3;4,5,6;7,8,9]) 0 0 3 0





-- theorem morePrev {y : ℕ} (i : Fin y) : i - 1 < y := by
-- omega

-- -- i stands for current row, j stands for specified column, y stands for the last row + 1, p stands for the row of the pivot
-- -- turns all numbers on column j below row i or p into 0
-- def turnAboveIntoZero [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ} (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (p : Fin y) (t : ℕ)
--   : Matrix (Fin y) (Fin z) α :=
--   if h1 : i - 1 = t then M
--   else
--     let iprev := (⟨i-1,morePrev i⟩ : Fin y)
--     if M iprev j = 0 then turnAboveIntoZero M iprev j p t
--     else
--       let M' := addMulRow M iprev p (-(M iprev j)/(M p j))
--       turnAboveIntoZero M' iprev j p t
-- termination_by i - t


-- theorem morePrev {y : ℕ} (i : Fin y) (hi : (i + 1: ℕ) ≠ y) : i + 1 < y := by
--   omega

-- theorem morePrev {y : ℕ} (i : Fin y) : i - 1 < y := by
--   omega

-- -- i stands for current row, j stands for specified column, y stands for the last row + 1, p stands for the row of the pivot
-- -- turns all numbers on column j below row i or p into 0
-- def turnAboveIntoZero [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ} (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (p : Fin y)
--   : Matrix (Fin y) (Fin z) α :=
--   -- if the current row is the last row, then return matrix
--   if h1 : (i : ℕ) = 0 then M
--   -- if the value of the position below is 0, move onto the next one below
--   else
--     let iprev := (⟨i - 1, morePrev i⟩ : Fin y)
--     if M iprev j = 0 then turnAboveIntoZero M iprev j p
--   -- if it is not 0, then make it into 0 and move on to the next one below with the changed matrix
--     else
--       let M' := addMulRow M iprev p (-(M iprev j)/(M p j))
--       turnAboveIntoZero M' iprev j p
-- termination_by i



-- -- i stands for current row, j stands for specified column, y stands for the last row + 1, p stands for the row of the pivot
-- -- turns all numbers on column j below row i or p into 0
-- def turnAboveIntoZero [DecidableEq α] [DivisionRing α] {y : ℕ} {z : ℕ} (M : Matrix (Fin y) (Fin z) α) (i : Fin y) (j : Fin z) (p : Fin y) (t : ℕ)
--   : Matrix (Fin y) (Fin z) α :=
--   -- if the current row is the last row, then return matrix
--   if h1 : i - 1 = t then M
--   -- if the value of the position below is 0, move onto the next one below
--   else
--     let iprev := (⟨i+1,lessSucc i h1⟩ : Fin y)
--     if M iprev j = 0 then turnAboveIntoZero M iprev j p t
--   -- if it is not 0, then make it into 0 and move on to the next one below with the changed matrix
--     else
--       let M' := addMulRow M iprev p (-(M iprev j)/(M p j))
--       turnAboveIntoZero M' iprev j p t
-- termination_by y - i
