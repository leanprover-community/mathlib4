/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Init

/-!
# Matrices as lists of rows

Computational definitions on matrices represented as lists of rows, `List (List α)`, for
tactics that certify facts about matrix literals.

## Main definitions
* `ListMatrix.dotProduct`
* `ListMatrix.transpose`
* `ListMatrix.mul`

## Implementation notes

The definitions in this file are intended for defining reflection certificates and should
not be used for theory interface.

`ListMatrix` namespace is used to avoid accidental collision with other downstream definitions.

Lean's `Array` is essentially a `List` within the kernel, so random access is slow; the `List`
carrier is chosen for easier inductive operations.

Reading an entry by position costs the kernel a walk of that length. Therefore, operations on
this representation need to be mindful of traversing the structure in an efficient order.

`ListMatrix.transpose` is defined by recursion on the rows with explicit padding rather than
through `List.transpose`, so that it reduces in the kernel. This is also more
efficient as it gives an `O(n^2)` transposition without any random access.
-/

@[expose] public section

@[simp]
theorem List.getD_rightpad {α : Type*} (n i : Nat) (a : α) (l : List α) :
    (l.rightpad n a).getD i a = l.getD i a := by
  grind [List.rightpad]

namespace Mathlib.Tactic.Matrix.ListMatrix

variable {α : Type*}

/-- The sum of `n` pointwise products of `l₁` and `l₂` padded by 0 without breaking early. -/
def dotProduct [Zero α] [Add α] [Mul α] : Nat → List α → List α → α
  | 0, _, _ => 0
  | n + 1, l₁, l₂ => l₁.headD 0 * l₂.headD 0 + dotProduct n l₁.tail l₂.tail

/-! Controlled unfolding helpers of `dotProduct` instead of asking the kernel to unfold,
which might unwantedly open `+`. -/
theorem dotProduct_zero [Zero α] [Add α] [Mul α] (l₁ l₂ : List α) : dotProduct 0 l₁ l₂ = 0 :=
  rfl

theorem dotProduct_succ_cons_cons [Zero α] [Add α] [Mul α] (n : Nat) (a b : α) (l₁ l₂ : List α) :
    dotProduct (n + 1) (a :: l₁) (b :: l₂) = a * b + dotProduct n l₁ l₂ :=
  rfl


/-- The transpose of a list of rows as `n` rows, where row `j` collects the `j`-th entries of
the input rows padded with `0`. -/
def transpose [Zero α] (n : Nat) (rows : List (List α)) : List (List α) :=
  match rows with
  | [] => List.replicate n []
  | row :: rows => List.zipWith (· :: ·) ((row.rightpad n 0).take n) (transpose n rows)

@[simp]
theorem length_transpose [Zero α] (n : Nat) (rows : List (List α)) :
    (transpose n rows).length = n := by
  induction rows <;> grind [transpose]

theorem getD_transpose [Zero α] {n j : Nat} (rows : List (List α)) (i : Nat) (hj : j < n) :
    ((transpose n rows).getD j []).getD i 0 = (rows.getD i []).getD j 0 := by
  induction rows generalizing i with
  | nil => simp [transpose, hj]
  | cons row rows ih =>
    rw [← List.getElem_eq_getD (i := j) (h := ?_)]
    · simp only [transpose, List.getElem_zipWith]
      cases i with
      | zero => grind [List.rightpad]
      | succ i =>
        simp only [List.getD_cons_succ, List.getElem_eq_getD []]
        exact ih i
    · simpa using hj

/-- The product of two lists of rows as `l` rows of `n` entries, each entry a dot product of
`m` terms, with `A` read as an `l × m` matrix and `B` as an `m × n` matrix. -/
def mul [Zero α] [Add α] [Mul α] (l m n : Nat) (A B : List (List α)) : List (List α) :=
  let Bt := transpose n B
  (A.rightpad l []).map fun rowA ↦ Bt.map (dotProduct m rowA)

theorem getD_mul [Zero α] [Add α] [Mul α] {l m n i j : Nat} (A B : List (List α)) (hi : i < l)
    (hj : j < n) :
    ((mul l m n A B).getD i []).getD j 0 =
      dotProduct m (A.getD i []) ((transpose n B).getD j []) := by
  rw [mul, ← List.getElem_eq_getD (i := i), List.getElem_map, List.getElem_eq_getD,
    List.getD_rightpad, ← List.getElem_eq_getD, List.getElem_map, List.getElem_eq_getD]
  · simp [hj]
  · grind [List.rightpad]

end Mathlib.Tactic.Matrix.ListMatrix
