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
operations to the matrix ones. A tactic states and certifies a fact on the lists, where the
kernel reduces by traversal, and bridges it to the `Matrix` statement by one of these lemmas,
so that the matrix is never evaluated as a function.

## Main definitions
* `FinVec.ofList`
* `ofLists`

## Main results
* `ofLists_transpose`
* `ofLists_mul`

## Implementation notes

The definitions recurse on the dimensions, so on literals they reduce in the kernel to the
`vecCons` form of the `!![…]` notation, and a literal in that notation is definitionally an
`ofLists` term.

When the elaboration of `!![…]` notation changes eventually, `FinVec.ofList` and `ofLists` will
become unnecessary.
-/

public section

-- opened outside the namespace, where `Matrix` resolves to the type's namespace rather than to
-- `Mathlib.Tactic.Matrix`
open Matrix

namespace Mathlib.Tactic.Matrix

variable {α : Type*}

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
@[expose] def ofLists [Zero α] (m n : ℕ) (rows : List (List α)) : Matrix (Fin m) (Fin n) α :=
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
theorem ListMatrix.dotProduct_eq [NonUnitalNonAssocSemiring α] (n : ℕ) (l₁ l₂ : List α) :
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
theorem ofLists_mul [NonUnitalNonAssocSemiring α] (l m n : ℕ) (A B : List (List α)) :
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

end Mathlib.Tactic.Matrix
