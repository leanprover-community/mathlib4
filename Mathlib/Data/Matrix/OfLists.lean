/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Data.Matrix.ListMatrix
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Matrices from lists of rows

`Matrix.ofLists` reads a list of rows as a `Matrix`, and the transpose and the product of such
matrices are computed on their lists of rows.

## Main definitions
* `FinVec.ofList`
* `Matrix.ofLists`

## Main results
* `Matrix.ofLists_transpose`
* `Matrix.ofLists_mul`

## Implementation notes

The definitions recurse on the dimensions, so on literals they reduce in the kernel to the
`vecCons` form of the `!![…]` notation.
-/

public section

variable {α : Type*}

open Matrix

/-- Construct a vector from the first `n` elements of a list, padded with `0`. -/
@[expose] def FinVec.ofList [Zero α] (n : ℕ) (l : List α) : Fin n → α :=
  match n, l with
  | 0, _ => ![]
  | n' + 1, [] => vecCons 0 (FinVec.ofList n' [])
  | n' + 1, a :: l' => vecCons a (FinVec.ofList n' l')

@[simp]
theorem FinVec.ofList_apply [Zero α] (n : ℕ) (l : List α) (i : Fin n) :
    FinVec.ofList n l i = l.getD i 0 := by
  induction n generalizing l with
  | zero => exact i.elim0
  | succ n ih => cases l <;> refine Fin.cases ?_ ?_ i <;> simp [FinVec.ofList, ih]

/-- Construct a matrix from the first `n` elements of the first `m` lists,
padded with `0`. -/
@[expose] def Matrix.ofLists [Zero α] (m n : ℕ) (rows : List (List α)) :
    Matrix (Fin m) (Fin n) α :=
  match m, rows with
  | 0, _ => of ![]
  | m' + 1, [] => of (vecCons (FinVec.ofList n []) (Matrix.ofLists m' n []))
  | m' + 1, row :: rows' => of (vecCons (FinVec.ofList n row) (Matrix.ofLists m' n rows'))

@[simp]
theorem Matrix.ofLists_apply [Zero α] (m n : ℕ) (rows : List (List α)) (i : Fin m) :
    ofLists m n rows i = FinVec.ofList n (rows.getD i []) := by
  induction m generalizing rows with
  | zero => exact i.elim0
  | succ m ih => cases rows <;> exact Fin.cases rfl (ih _) i

@[simp]
theorem ListMatrix.dotProduct_eq [NonUnitalNonAssocSemiring α] (n : ℕ) (l₁ l₂ : List α) :
    ListMatrix.dotProduct n l₁ l₂ = FinVec.ofList n l₁ ⬝ᵥ FinVec.ofList n l₂ := by
  induction n generalizing l₁ l₂ with
  | zero => simp [ListMatrix.dotProduct]
  | succ n ih => cases l₁ <;> cases l₂ <;> simp [FinVec.ofList, ListMatrix.dotProduct, ← ih]

@[simp]
theorem Matrix.ofLists_transpose [Zero α] (m n : ℕ) (rows : List (List α)) :
    ofLists n m (ListMatrix.transpose n rows) = (ofLists m n rows)ᵀ := by
  ext j i
  simpa using ListMatrix.getD_transpose rows i j.isLt

@[simp]
theorem Matrix.ofLists_mul [NonUnitalNonAssocSemiring α] (l m n : ℕ) (A B : List (List α)) :
    ofLists l n (ListMatrix.mul m n A B) = ofLists l m A * ofLists m n B := by
  ext i j
  rw [mul_apply', ofLists_apply, ofLists_apply, FinVec.ofList_apply]
  have hcol :
      (fun k ↦ ofLists m n B k j) = FinVec.ofList m ((ListMatrix.transpose n B).getD j []) := by
    funext k
    rw [ofLists_apply, FinVec.ofList_apply, FinVec.ofList_apply,
      ListMatrix.getD_transpose B k j.isLt]
  rw [hcol, ← ListMatrix.dotProduct_eq, ListMatrix.mul]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases A[i]? <;> simp [ListMatrix.dotProduct]
