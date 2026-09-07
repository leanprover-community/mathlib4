/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

/-!
# Matrices as lists of rows

Operations on matrices represented as lists of rows, `List (List α)`, importing nothing
beyond core Lean.

## Main definitions
* `List.dotProduct`, `ListMatrix.transpose`, `ListMatrix.mul`.

## Implementation notes

Lean's `Array` is essentially a `List` within the kernel, so random access is slow; the `List`
carrier is chosen for easier inductive operations. `ListMatrix.transpose` is defined by
recursion on the rows with explicit padding rather than through `List.transpose`, so that it
reduces in the kernel.
-/

public section

universe u

variable {α : Type u}

/-- The dot product of the first `n` entries of two lists. -/
@[expose] def List.dotProduct [Zero α] [Add α] [Mul α] (n : Nat) (l₁ l₂ : List α) : α :=
  ((List.zipWith (· * ·) l₁ l₂).take n).sum

@[simp]
theorem List.dotProduct_zero [Zero α] [Add α] [Mul α] (l₁ l₂ : List α) :
    l₁.dotProduct 0 l₂ = 0 :=
  rfl

@[simp]
theorem List.dotProduct_succ_cons_cons [Zero α] [Add α] [Mul α] (n : Nat) (a b : α)
    (l₁ l₂ : List α) : (a :: l₁).dotProduct (n + 1) (b :: l₂) = a * b + l₁.dotProduct n l₂ :=
  rfl

/-- The transpose of a list of rows as `n` rows, where row `j` collects the `j`-th entries of
the input rows padded with `0`. -/
@[expose] def ListMatrix.transpose [Zero α] (n : Nat) (rows : List (List α)) :
    List (List α) :=
  match rows with
  | [] => List.replicate n []
  | row :: rows => List.zipWith (· :: ·) ((row.rightpad n 0).take n) (transpose n rows)

@[simp]
theorem ListMatrix.length_transpose [Zero α] (n : Nat) (rows : List (List α)) :
    (transpose n rows).length = n := by
  induction rows <;> grind [transpose]

theorem ListMatrix.getD_transpose [Zero α] {n j : Nat} (rows : List (List α)) (i : Nat)
    (hj : j < n) : ((transpose n rows).getD j []).getD i 0 = (rows.getD i []).getD j 0 := by
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
@[expose] def ListMatrix.mul [Zero α] [Add α] [Mul α] (m n : Nat) (A B : List (List α)) :
    List (List α) :=
  let BT := transpose n B
  A.map fun rowA ↦ BT.map (rowA.dotProduct m)
