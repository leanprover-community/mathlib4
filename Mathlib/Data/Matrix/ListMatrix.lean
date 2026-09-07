/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.List.GetD

/-!
# List-based representation of matrices and operations on them

This file defines a representation of matrices as lists of rows, `List (List α)`, and some
associated operations on them. The definitions recurse on the dimensions, so on literals they
reduce in the kernel to the `vecCons` form of the `!![…]` notation.

## Main definitions
* `Matrix.ofLists`: convert a list of rows to a `Matrix`.
* `ListMatrix.mul`: multiplying two lists of rows.

## Main results
* `Matrix.ofLists_mul`: `ListMatrix.mul` agrees with the matrix product under `Matrix.ofLists`.

## Implementation notes

Note that Lean's `Array` is essentially a `List` within the kernel, therefore random access is
slow. The `List` carrier is chosen over `Array` for easier inductive operations.

`ListMatrix.transpose` is defined by recursion on the rows with explicit padding rather than
through `List.transpose`, so that it reduces in the kernel.

All conversions from the list-based version to Mathlib types ignore excessive entries and
pad the missing entries with 0.
-/

public section

variable {α : Type*}

open Matrix

/-- Construct a vector from the first `n` elements of a list, padded with `0`. -/
@[expose] def List.toVec [Zero α] (n : ℕ) (l : List α) : Fin n → α :=
  match n, l with
  | 0, _ => ![]
  | n' + 1, [] => vecCons 0 (List.toVec n' [])
  | n' + 1, a :: l' => vecCons a (l'.toVec n')

@[simp]
theorem List.toVec_apply [Zero α] (n : ℕ) (l : List α) (i : Fin n) : l.toVec n i = l.getD i 0 := by
  induction n generalizing l with
  | zero => exact i.elim0
  | succ n ih => cases l <;> refine Fin.cases ?_ ?_ i <;> simp [List.toVec, ih]

/-- Construct a matrix from the first `n` elements of the first `m` lists,
padded with `0`. -/
@[expose] def Matrix.ofLists [Zero α] (m n : ℕ) (rows : List (List α)) :
    Matrix (Fin m) (Fin n) α :=
  match m, rows with
  | 0, _ => of ![]
  | m' + 1, [] => of (vecCons (List.toVec n []) (Matrix.ofLists m' n []))
  | m' + 1, row :: rows' => of (vecCons (row.toVec n) (Matrix.ofLists m' n rows'))

@[simp]
theorem Matrix.ofLists_apply [Zero α] (m n : ℕ) (rows : List (List α)) (i : Fin m) :
    ofLists m n rows i = (rows.getD i []).toVec n := by
  induction m generalizing rows with
  | zero => exact i.elim0
  | succ m ih => cases rows <;> exact Fin.cases rfl (ih _) i

/-- The dot product of the first `n` entries of two lists. -/
@[expose] def List.dotProduct [Zero α] [Add α] [Mul α] (n : ℕ) (l₁ l₂ : List α) : α :=
  ((List.zipWith (· * ·) l₁ l₂).take n).sum

@[simp]
theorem List.dotProduct_zero [Zero α] [Add α] [Mul α] (l₁ l₂ : List α) :
    l₁.dotProduct 0 l₂ = 0 :=
  rfl

@[simp]
theorem List.dotProduct_succ_cons_cons [Zero α] [Add α] [Mul α] (n : ℕ) (a b : α)
    (l₁ l₂ : List α) : (a :: l₁).dotProduct (n + 1) (b :: l₂) = a * b + l₁.dotProduct n l₂ :=
  rfl

@[simp]
theorem List.dotProduct_eq [NonUnitalNonAssocSemiring α] (n : ℕ) (l₁ l₂ : List α) :
    l₁.dotProduct n l₂ = l₁.toVec n ⬝ᵥ l₂.toVec n := by
  induction n generalizing l₁ l₂ with
  | zero => simp [List.dotProduct]
  | succ n ih => cases l₁ <;> cases l₂ <;> simp [List.toVec, List.dotProduct, ← ih]

/-- The transpose of a list of rows as `n` rows, where row `j` collects the `j`-th entries of
the input rows padded with `0`. -/
@[expose] def ListMatrix.transpose [Zero α] (n : ℕ) (rows : List (List α)) : List (List α) :=
  match rows with
  | [] => List.replicate n []
  | row :: rows => List.zipWith (· :: ·) ((row.rightpad n 0).take n) (transpose n rows)

@[simp]
theorem ListMatrix.length_transpose [Zero α] (n : ℕ) (rows : List (List α)) :
    (transpose n rows).length = n := by
  induction rows <;> grind [transpose]

theorem ListMatrix.getD_transpose [Zero α] {n j : ℕ} (rows : List (List α)) (i : ℕ)
    (hj : j < n) : ((transpose n rows).getD j []).getD i 0 = (rows.getD i []).getD j 0 := by
  induction rows generalizing i with
  | nil => simp [transpose, hj]
  | cons row rows ih =>
    rw [transpose, List.getD_eq_getElem (n := j), List.getElem_zipWith]
    · cases i with
      | zero =>
        simp only [List.getD_cons_zero]
        grind [List.rightpad]
      | succ i =>
        simp only [List.getD_cons_succ]
        rw [← ih, List.getD_eq_getElem (n := j)]
    · simp [hj]
      omega

@[simp]
theorem Matrix.ofLists_transpose [Zero α] (m n : ℕ) (rows : List (List α)) :
    ofLists n m (ListMatrix.transpose n rows) = (ofLists m n rows)ᵀ := by
  ext j i
  simpa using ListMatrix.getD_transpose rows i j.isLt

/-- The product of two lists of rows, with `A` interpreted as having `m` columns and `B` as an
`m × n` matrix. -/
@[expose] def ListMatrix.mul [Zero α] [Add α] [Mul α] (m n : ℕ) (A B : List (List α)) :
    List (List α) :=
  let BT := transpose n B
  A.map fun rowA ↦ BT.map (rowA.dotProduct m)

@[simp]
theorem Matrix.ofLists_mul [NonUnitalNonAssocSemiring α] (l m n : ℕ) (A B : List (List α)) :
    ofLists l n (ListMatrix.mul m n A B) = ofLists l m A * ofLists m n B := by
  ext i j
  rw [mul_apply', ofLists_apply, ofLists_apply, List.toVec_apply]
  have hcol : (fun k ↦ ofLists m n B k j) = ((ListMatrix.transpose n B).getD j []).toVec m := by
    funext k
    rw [ofLists_apply, List.toVec_apply, List.toVec_apply, ListMatrix.getD_transpose B k j.isLt]
  rw [hcol, ← List.dotProduct_eq, ListMatrix.mul]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases A[i]? <;> simp [List.dotProduct]
