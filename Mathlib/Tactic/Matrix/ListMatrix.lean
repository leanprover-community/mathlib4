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

`ListMatrix` namespace is used to avoid accidental collision with other downstream definitions.

## Main definitions
* `ListMatrix.dotProduct`
* `ListMatrix.transpose`
* `ListMatrix.mul`

## Implementation notes

Lean's `Array` is essentially a `List` within the kernel, so random access is slow; the `List`
carrier is chosen for easier inductive operations.

Reading an entry by position costs the kernel a walk of that length. Therefore, operations on
this representation needs to be mindful of traversing the structure in an efficient order.

`ListMatrix.transpose` is defined by recursion on the rows with explicit padding rather than
through `List.transpose` from Batteries, so that it reduces in the kernel. This is also more
efficient as it gives a genuine `O(n^2)` transposition without any random access.
-/

public section

namespace Mathlib.Tactic.Matrix.ListMatrix

variable {α : Type*}

/-- The dot product of the first `n` entries of two lists. -/
@[expose] def dotProduct [Zero α] [Add α] [Mul α] (n : Nat) (l₁ l₂ : List α) : α :=
  ((List.zipWith (· * ·) l₁ l₂).take n).sum

theorem dotProduct_zero [Zero α] [Add α] [Mul α] (l₁ l₂ : List α) : dotProduct 0 l₁ l₂ = 0 :=
  rfl

theorem dotProduct_succ_cons_cons [Zero α] [Add α] [Mul α] (n : Nat) (a b : α) (l₁ l₂ : List α) :
    dotProduct (n + 1) (a :: l₁) (b :: l₂) = a * b + dotProduct n l₁ l₂ :=
  rfl

/-- The transpose of a list of rows as `n` rows, where row `j` collects the `j`-th entries of
the input rows padded with `0`. -/
@[expose] def transpose [Zero α] (n : Nat) (rows : List (List α)) : List (List α) :=
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
    have hlen :
        j < (List.zipWith (· :: ·) ((row.rightpad n 0).take n) (transpose n rows)).length := by
      simp only [List.length_zipWith, List.length_take, List.length_rightpad, length_transpose]
      lia
    rw [transpose, List.getD_eq_getElem?_getD (i := j), List.getElem?_eq_getElem hlen,
      Option.getD_some, List.getElem_zipWith]
    cases i with
    | zero =>
      simp only [List.getD_cons_zero]
      grind [List.rightpad]
    | succ i =>
      simp only [List.getD_cons_succ]
      rw [← ih, List.getD_eq_getElem?_getD (i := j),
        List.getElem?_eq_getElem (by simp only [length_transpose]; exact hj), Option.getD_some]

/-- The product of two lists of rows, with `A` interpreted as having `m` columns and `B` as an
`m × n` matrix. -/
@[expose] def mul [Zero α] [Add α] [Mul α] (m n : Nat) (A B : List (List α)) :
    List (List α) :=
  let BT := transpose n B
  A.map fun rowA ↦ BT.map (dotProduct m rowA)

end Mathlib.Tactic.Matrix.ListMatrix
