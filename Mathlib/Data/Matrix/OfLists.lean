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

`Matrix.ofLists` reads a list of rows as a `Matrix`. The definitions recurse on the dimensions,
so on literals they reduce in the kernel to the `vecCons` form of the `!![…]` notation, and
the results compute the transpose and the product of such matrices on their lists of rows.

## Main definitions
* `List.toVec`, `Matrix.ofLists`.

## Main results
* `Matrix.ofLists_transpose`, `Matrix.ofLists_mul`.
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

@[simp]
theorem List.dotProduct_eq [NonUnitalNonAssocSemiring α] (n : ℕ) (l₁ l₂ : List α) :
    l₁.dotProduct n l₂ = l₁.toVec n ⬝ᵥ l₂.toVec n := by
  induction n generalizing l₁ l₂ with
  | zero => simp [List.dotProduct]
  | succ n ih => cases l₁ <;> cases l₂ <;> simp [List.toVec, List.dotProduct, ← ih]

@[simp]
theorem Matrix.ofLists_transpose [Zero α] (m n : ℕ) (rows : List (List α)) :
    ofLists n m (ListMatrix.transpose n rows) = (ofLists m n rows)ᵀ := by
  ext j i
  simpa using ListMatrix.getD_transpose rows i j.isLt

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
