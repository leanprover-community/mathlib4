/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Matrix.ListMatrix

/-!
# Matrices from lists of rows

`ofLists` reads a list of rows as a `Matrix`, and the results here transport the list
operations to the matrix ones.

## Main definitions
* `FinVec.ofList`
* `ofLists`

## Main results
* `Matrix.mul_apply_row_col`
* `ofLists_transpose`
* `ofLists_mul`

## Implementation notes

The definitions recurse on the dimensions, so on literals they reduce in the kernel to the
`vecCons` form of the `!![…]` notation, and a literal in that notation is definitionally an
`ofLists` term.

When the elaboration of the `!![…]` notation changes, `FinVec.ofList` and `ofLists` will become
unnecessary.
-/

@[expose] public section

-- opened outside the namespace, where `Matrix` resolves to the type's namespace rather than to
-- `Mathlib.Tactic.Matrix`
open Matrix

theorem Matrix.mul_apply_row_col {l m n α : Type*} [Fintype m] [Mul α] [AddCommMonoid α]
    (M : Matrix l m α) (N : Matrix m n α) (i : l) (k : n) : (M * N) i k = M i ⬝ᵥ N.col k :=
  rfl

namespace Mathlib.Tactic.Matrix

variable {α : Type*}

/-- Construct a vector from the first `n` elements of a list, padded with `0`. -/
def FinVec.ofList [Zero α] (n : ℕ) (l : List α) : Fin n → α :=
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
def ofLists [Zero α] (m n : ℕ) (rows : List (List α)) : Matrix (Fin m) (Fin n) α :=
  match m, rows with
  | 0, _ => of ![]
  | m' + 1, [] => of (vecCons (FinVec.ofList n []) (ofLists m' n []))
  | m' + 1, row :: rows' => of (vecCons (FinVec.ofList n row) (ofLists m' n rows'))

@[simp]
theorem ofLists_apply [Zero α] (m n : ℕ) (rows : List (List α)) (i : Fin m) :
    ofLists m n rows i = FinVec.ofList n (rows.getD i []) := by
  induction m generalizing rows with
  | zero => exact i.elim0
  | succ m ih => cases rows <;> exact Fin.cases rfl (ih _) i

@[simp]
theorem ListMatrix.dotProduct_eq [Mul α] [AddCommMonoid α] (n : ℕ) (l₁ l₂ : List α) :
    ListMatrix.dotProduct n l₁ l₂ = FinVec.ofList n l₁ ⬝ᵥ FinVec.ofList n l₂ := by
  induction n generalizing l₁ l₂ with
  | zero => simp [ListMatrix.dotProduct]
  | succ n ih => cases l₁ <;> cases l₂ <;> simp [FinVec.ofList, ListMatrix.dotProduct, ← ih]

@[simp]
theorem ofLists_transpose [Zero α] (m n : ℕ) (rows : List (List α)) :
    ofLists n m (ListMatrix.transpose n rows) = (ofLists m n rows)ᵀ := by
  ext j i
  simpa using ListMatrix.getD_transpose rows i j.isLt

@[simp]
theorem ofLists_mul [Mul α] [AddCommMonoid α] (l m n : ℕ) (A B : List (List α)) :
    ofLists l n (ListMatrix.mul l m n A B) = ofLists l m A * ofLists m n B := by
  ext i j
  simp only [Matrix.mul_apply_row_col, ← row_transpose, ← ofLists_transpose, row_apply',
    ofLists_apply, FinVec.ofList_apply, ← ListMatrix.dotProduct_eq,
    ListMatrix.getD_mul A B i.isLt j.isLt]

end Mathlib.Tactic.Matrix
