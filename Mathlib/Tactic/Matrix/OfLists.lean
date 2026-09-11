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

## Main results

* `ofLists_transpose`
* `ofLists_mul`

## Implementation notes

The definitions recurse on the dimensions, so on literals they reduce in the kernel to the
`vecCons` form of the `!![…]` notation, and a literal in that notation is definitionally an
`ofLists` term.

When the elaboration of the `!![…]` notation changes to list-based, `ofList` and `ofLists` will
become unnecessary.
-/

@[expose] public section

-- opened outside the namespace, where `Matrix` resolves to the type's namespace rather than to
-- `Mathlib.Tactic.Matrix`
open Matrix

namespace Mathlib.Tactic.Matrix

variable {α : Type*}

/-- Construct a vector from the first `n` elements of a list, padded with `0`. -/
def ofList [Zero α] : (n : ℕ) → List α → Fin n → α
  | 0, _ => ![]
  | n + 1, [] => vecCons 0 (ofList n [])
  | n + 1, a :: l => vecCons a (ofList n l)

@[simp]
theorem ofList_apply [Zero α] (n : ℕ) (l : List α) (i : Fin n) : ofList n l i = l.getD i 0 := by
  induction n generalizing l with
  | zero => exact i.elim0
  | succ n ih => cases l <;> refine Fin.cases ?_ ?_ i <;> simp [ofList, ih]

/-- The first `n` elements of the first `m` lists as a function of two indices, padded with
`0`. -/
def ofListsFun [Zero α] : (m n : ℕ) → List (List α) → Fin m → Fin n → α
  | 0, _, _ => ![]
  | m + 1, n, [] => vecCons (ofList n []) (ofListsFun m n [])
  | m + 1, n, row :: rows => vecCons (ofList n row) (ofListsFun m n rows)

/-- Construct a matrix from the first `n` elements of the first `m` lists, padded with `0`. -/
def ofLists [Zero α] (m n : ℕ) (rows : List (List α)) : Matrix (Fin m) (Fin n) α :=
  of (ofListsFun m n rows)

@[simp]
theorem ofLists_apply [Zero α] (m n : ℕ) (rows : List (List α)) (i : Fin m) :
    ofLists m n rows i = ofList n (rows.getD i []) := by
  induction m generalizing rows with
  | zero => exact i.elim0
  | succ m ih => cases rows <;> exact Fin.cases rfl (ih _) i

@[simp]
theorem ListMatrix.dotProduct_eq [Mul α] [AddCommMonoid α] (n : ℕ) (l₁ l₂ : List α) :
    ListMatrix.dotProduct n l₁ l₂ = ofList n l₁ ⬝ᵥ ofList n l₂ := by
  induction n generalizing l₁ l₂ with
  | zero => simp [ListMatrix.dotProduct]
  | succ n ih => cases l₁ <;> cases l₂ <;> simp [ofList, ListMatrix.dotProduct, ← ih]

@[simp]
theorem ofLists_transpose [Zero α] (m n : ℕ) (rows : List (List α)) :
    ofLists n m (ListMatrix.transpose n rows) = (ofLists m n rows)ᵀ := by
  ext j i
  simpa using ListMatrix.getD_transpose rows i j.isLt

@[simp]
theorem ofLists_mul [Mul α] [AddCommMonoid α] (l m n : ℕ) (A B : List (List α)) :
    ofLists l n (ListMatrix.mul l m n A B) = ofLists l m A * ofLists m n B := by
  ext i j
  rw [mul_apply', ← col_apply' (ofLists m n B) j]
  simp only [← row_transpose, ← ofLists_transpose, row_apply', ofLists_apply, ofList_apply,
    ← ListMatrix.dotProduct_eq, ListMatrix.getD_mul A B i.isLt j.isLt]

theorem ofLists_eq_zero_of_lt [Zero α] {m : ℕ} (rows : List (List α))
    (h : ∀ x ∈ ListMatrix.aboveDiagonal 0 rows, x = 0) {i j : Fin m} (hij : i < j) :
    ofLists m m rows i j = 0 := by
  rw [ofLists_apply, ofList_apply]
  exact ListMatrix.getD_eq_zero_of_aboveDiagonal h (by simpa using hij)

theorem diag_ofLists_ne_zero [Zero α] {m : ℕ} (rows : List (List α))
    (h : ∀ x ∈ ListMatrix.diagonal 0 m rows, x ≠ 0) (i : Fin m) :
    (ofLists m m rows).diag i ≠ 0 := by
  rw [diag_apply, ofLists_apply, ofList_apply]
  simpa using ListMatrix.getD_ne_zero_of_diagonal h i.isLt

end Mathlib.Tactic.Matrix
