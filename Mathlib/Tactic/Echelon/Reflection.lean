/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Data.List.Sort
public import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot
public import Mathlib.Tactic.Matrix.OfLists

/-!
# Reflection certificates for the echelon decomposition

The list-based certificates for a part of `Echelon.Decomposition` and their bridge lemmas.

## Main definitions

- `IsLowerTriangularDiagList`: a list of rows is lower triangular with nonzero diagonal.
- `IsPivotedList`: a list of rows has the given pivot columns.
- `pivotOfList`: the pivot function corresponding to a given list of pivot columns.

## Implementation notes

The two conditions are kept as separate predicates for optimised checks.
The pivot cert states that each row is 0 up to its pivot column as the one equation
`row = List.replicate k 0 ++ d :: suffix`, which the kernel checks in one traversal of the row.
The lower-triangularity check requires each row to be 0 beyond the diagonal, so it skips the
prefix by `drop`.
-/

public section

open Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Echelon

variable {α : Type*}

/-! ### Lower triangularity and nonzero diagonal of `L`

Both conditions read the same suffix of each row, so one sweep certifies them together.
-/

/-- `c` rows starting at row `k`, each with a nonzero entry at its diagonal position and zeros
after it to the end of the row. -/
inductive IsLowerTriangularDiagList [Zero α] : ℕ → ℕ → List (List α) → Prop
  | nil {k : ℕ} {rows : List (List α)} : IsLowerTriangularDiagList k 0 rows
  | cons {k c : ℕ} {row : List α} {rows : List (List α)} {d : α}
      (hdrop : row.drop k = d :: List.replicate c 0) (hd : d ≠ 0)
      (h : IsLowerTriangularDiagList (k + 1) c rows) :
      IsLowerTriangularDiagList k (c + 1) (row :: rows)

/-- Lookup specification for `IsLowerTriangularDiagList`. -/
theorem getD_of_isLowerTriangularDiagList [Zero α] {k c i : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiagList k c rows) (hi : i < c) :
    (rows.getD i []).getD (k + i) 0 ≠ 0 ∧
      ∀ j, k + i < j → (rows.getD i []).getD j 0 = 0 := by
  induction h generalizing i with
  | nil => lia
  | @cons k c row rows d hdrop hd h ih =>
    cases i with
    | zero =>
      refine ⟨?_, fun j hj ↦ ?_⟩
      · have := List.getElem?_drop (xs := row) (i := k) (j := 0)
        grind
      · have := List.getElem?_drop (xs := row) (i := k) (j := j - k)
        grind
    | succ i => grind

theorem isLowerTriangular_ofLists [Zero α] {m : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiagList 0 m rows) : (ofLists m m rows).IsLowerTriangular := by
  intro i j hij
  rw [ofLists_apply, ofList_apply]
  exact (getD_of_isLowerTriangularDiagList h i.isLt).2 j (by simpa using hij)

theorem diag_ofLists_ne_zero [Zero α] {m : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiagList 0 m rows) (i : Fin m) : (ofLists m m rows).diag i ≠ 0 := by
  simpa [ofLists_apply, ofList_apply] using (getD_of_isLowerTriangularDiagList h i.isLt).1

/-! ### Pivots of `U` -/

variable {n : ℕ}

/-- The rows with a nonzero entry at their pivot columns and zeros before it, then the rows
beyond the pivot list (all 0). -/
inductive IsPivotedList [Zero α] : List (Fin n) → List (List α) → Prop
  | nil {rows : List (List α)} (hz : rows = rows.map fun _ ↦ List.replicate n 0) :
      IsPivotedList [] rows
  | cons {k : Fin n} {ks : List (Fin n)} {row : List α} {rows : List (List α)} {d : α}
      {suffix : List α} (hrow : row = List.replicate k 0 ++ d :: suffix) (hd : d ≠ 0)
      (h : IsPivotedList ks rows) : IsPivotedList (k :: ks) (row :: rows)

/-- The pivot function of the list of pivot columns. `WithTop (Fin n)` is `Option (Fin n)`, so
the lookup `cols[i]?` is the value. -/
@[expose] def pivotOfList (cols : List (Fin n)) (i : ℕ) : WithTop (Fin n) := cols[i]?

/-- Lookup specification for `IsPivotedList`. -/
theorem getD_of_isPivotedList [Zero α] {cols : List (Fin n)} {rows : List (List α)}
    (h : IsPivotedList cols rows) (i : ℕ) :
    (∀ j : Fin n, ↑j < pivotOfList cols i → (rows.getD i []).getD j 0 = 0) ∧
      ∀ c : Fin n, pivotOfList cols i = c → (rows.getD i []).getD c 0 ≠ 0 := by
  induction h generalizing i with
  | nil hz =>
    simp only [List.map_const'] at hz
    grind [pivotOfList, WithTop.none_eq_top, WithTop.coe_lt_top]
  | @cons k ks row rows d suffix hrow hd h ih =>
    cases i with
    | zero =>
      refine ⟨fun j hj ↦ ?_, fun c hc ↦ ?_⟩
      · have hjk : (j : ℕ) < k := Fin.lt_def.mp (WithTop.coe_lt_coe.mp hj)
        grind
      · obtain rfl : k = c := WithTop.coe_eq_coe.mp hc
        grind
    | succ i => exact ih i

theorem pivotOfList_lt_pivotOfList {cols : List (Fin n)} (hsorted : cols.SortedLT) {i j : ℕ}
    (hij : i < j) (hj : pivotOfList cols j ≠ ⊤) : pivotOfList cols i < pivotOfList cols j := by
  grind [pivotOfList, List.SortedLT.getElem_lt_getElem_iff, WithTop.coe_lt_coe, WithTop.some_eq_coe,
    WithTop.none_eq_top]

theorem pivotOfList_mono_of_sortedLT {cols : List (Fin n)} (hsorted : cols.SortedLT) :
    Monotone (pivotOfList cols) := by
  refine monotone_nat_of_le_succ fun i ↦ ?_
  have := pivotOfList_lt_pivotOfList hsorted (Nat.lt_succ_self i)
  grind [le_top]

theorem isPivotedBy_ofLists [Zero α] {m : ℕ} {rows : List (List α)} {cols : List (Fin n)}
    (hsorted : cols.SortedLT) (h : IsPivotedList cols rows) :
    (ofLists m n rows).IsPivotedBy fun i : Fin m ↦ pivotOfList cols i := by
  refine Matrix.isPivotedBy_iff.mpr ⟨?_, fun _ _ _ hj hij ↦ ?_, fun i ↦ ?_⟩
  · exact (pivotOfList_mono_of_sortedLT hsorted).comp Fin.val_strictMono.monotone
  · exact pivotOfList_lt_pivotOfList hsorted hij hj
  · simpa only [ofLists_apply, ofList_apply] using getD_of_isPivotedList h i

end Mathlib.Tactic.Echelon
