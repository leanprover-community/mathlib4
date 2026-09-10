/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Data.Nat.Notation

/-!
# List-based matrix representation and computation

An implementation of a list-based matrix representation and computation for tactics that certify
facts about matrix literals.

## Implementation notes

The definitions in this file are intended for defining reflection certificates only and should
not be used for any theory.

`ListMatrix` namespace is used to avoid accidental collision with other downstream definitions.

Lean's `Array` is essentially a `List` within the kernel, so random access is slow; the `List`
carrier is chosen for easier inductive operations.

Reading an entry by position costs the kernel a walk of that length. Therefore, operations on
this representation need to be mindful of traversing the structure in an efficient order.
-/

@[expose] public section

namespace Mathlib.Tactic.Matrix.ListMatrix

variable {α : Type*}

/-- A term for the sum of exactly `n` pointwise products of `l₁` and `l₂` padded with 0. This allows
its bridge lemma to be provable without `zero_mul`, which minimises the instance strength. -/
def dotProduct [Mul α] [Add α] [Zero α] : ℕ → List α → List α → α
  | 0, _, _ => 0
  | n + 1, l₁, l₂ => l₁.headD 0 * l₂.headD 0 + dotProduct n l₁.tail l₂.tail

/-! Controlled unfolding helpers of `dotProduct` -/

theorem dotProduct_zero [Mul α] [Add α] [Zero α] (l₁ l₂ : List α) : dotProduct 0 l₁ l₂ = 0 :=
  rfl

/- This is shaped to take the proof for the smaller dot product as an argument to produce a
smaller proof term for the kernel check, as this avoids requiring `Eq.trans` and `congrArg` glue
at each step. -/
theorem dotProduct_succ_cons_cons [Mul α] [Add α] [Zero α] {n : ℕ} (a b : α) {l₁ l₂ : List α}
    {c : α} (h : dotProduct n l₁ l₂ = c) : dotProduct (n + 1) (a :: l₁) (b :: l₂) = a * b + c :=
  congrArg (a * b + ·) h

/-- The transpose of a list of rows as `n` rows, where row `j` collects the `j`-th entries of
the input rows padded with `0`. Defined by recursion on the rows with explicit padding rather than
through Batteries' `List.transpose`, so that it reduces in the kernel. This is also more
efficient as it gives an `O(nm)` transposition without any random access. -/
def transpose [Zero α] (n : ℕ) : List (List α) → List (List α)
  | [] => List.replicate n []
  | row :: rows => List.zipWith List.cons ((row.rightpad n 0).take n) (transpose n rows)

@[simp]
theorem length_transpose [Zero α] (n : ℕ) (rows : List (List α)) :
    (transpose n rows).length = n := by
  induction rows <;> grind [transpose]

theorem getD_transpose [Zero α] {n j : ℕ} (rows : List (List α)) (i : ℕ) (hj : j < n) :
    ((transpose n rows).getD j []).getD i 0 = (rows.getD i []).getD j 0 := by
  induction rows generalizing i with
  | nil => simp [transpose, hj]
  | cons row tl ih =>
    rw [← List.getElem_eq_getD (i := j) (h := ?_)]
    · simp only [transpose, List.getElem_zipWith]
      cases i with
      | zero => grind [List.rightpad]
      | succ k =>
        simp only [List.getD_cons_succ, List.getElem_eq_getD []]
        exact ih k
    · simpa using hj

/-- The product of two lists of rows as `l` rows of `n` entries, each entry a dot product of
`m` terms, with `A` read as an `l × m` matrix and `B` as an `m × n` matrix. -/
def mul [Mul α] [Add α] [Zero α] (l m n : ℕ) (A B : List (List α)) : List (List α) :=
  let Bt := transpose n B
  (A.rightpad l []).map fun row ↦ Bt.map (dotProduct m row)

theorem getD_mul [Mul α] [Add α] [Zero α] {l m n i j : ℕ} (A B : List (List α)) (hi : i < l)
    (hj : j < n) :
    ((mul l m n A B).getD i []).getD j 0 =
      dotProduct m (A.getD i []) ((transpose n B).getD j []) := by
  have hA : (A.rightpad l []).getD i [] = A.getD i [] := by grind [List.rightpad]
  rw [mul, ← List.getElem_eq_getD (i := i), List.getElem_map, List.getElem_eq_getD, hA,
    ← List.getElem_eq_getD, List.getElem_map, List.getElem_eq_getD]
  · simp [hj]
  · grind [List.rightpad]

end Mathlib.Tactic.Matrix.ListMatrix
