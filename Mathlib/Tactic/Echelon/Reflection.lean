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

The conditions of `Echelon.Decomposition` on a matrix given as a list of rows, each a sweep along
the rows, with a bridge lemma to the condition on `ofLists`.
-/

@[expose] public section

open Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Echelon

variable {α : Type*}

/-! ### Lower triangularity and nonzero diagonal of `L`

Both conditions read the same suffix of each row, so they are certified together: one sweep whose
cell for row `k` holds the nonzero diagonal entry and the equation of the zeros after it, which
the kernel checks in one pass over the rows as one term. -/

/-- `c` rows starting at row `k`, each with a nonzero entry at its diagonal position and zeros
after it to the end of the row. -/
def IsLowerTriangularDiagList [Zero α] : (k c : ℕ) → (rows : List (List α)) → Prop
  | _, 0, _ => True
  | _, _ + 1, [] => False
  | k, c + 1, row :: rows =>
    match row.drop k with
    | [] => False
    | d :: zs => d ≠ 0 ∧ zs = List.replicate c 0 ∧ IsLowerTriangularDiagList (k + 1) c rows

theorem getD_of_isLowerTriangularDiagList [Zero α] {k c i : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiagList k c rows) (hi : i < c) :
    (rows.getD i []).getD (k + i) 0 ≠ 0 ∧ ∀ j, k + i < j → (rows.getD i []).getD j 0 = 0 := by
  induction c generalizing k i rows with
  | zero => simp at hi
  | succ c ih =>
    cases rows with
    | nil => simp [IsLowerTriangularDiagList] at h
    | cons row rows =>
      cases hdk : row.drop k with
      | nil => simp [IsLowerTriangularDiagList, hdk] at h
      | cons d zs =>
        simp only [IsLowerTriangularDiagList, hdk] at h
        obtain ⟨hd, hz, hrest⟩ := h
        cases i with
        | zero =>
          rw [List.getD_cons_zero]
          have := List.getElem?_drop (xs := row) (i := k) (j := 0)
          refine ⟨by grind, fun j hj ↦ ?_⟩
          have := List.getElem?_drop (xs := row) (i := k) (j := j - k)
          grind
        | succ i =>
          rw [List.getD_cons_succ, ← Nat.add_assoc, Nat.add_right_comm]
          exact ih hrest (by lia)

theorem isLowerTriangular_ofLists [Zero α] {m : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiagList 0 m rows) : (ofLists m m rows).IsLowerTriangular := by
  intro i j hij
  rw [ofLists_apply, ofList_apply]
  exact (getD_of_isLowerTriangularDiagList h i.isLt).2 j (by simpa using hij)

theorem diag_ofLists_ne_zero [Zero α] {m : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiagList 0 m rows) (i : Fin m) : (ofLists m m rows).diag i ≠ 0 := by
  rw [Matrix.diag_apply, ofLists_apply, ofList_apply]
  simpa using (getD_of_isLowerTriangularDiagList h i.isLt).1

/-! ### Pivots of `U` -/

variable {n : ℕ}

/-- `l` split at `k` in one traversal instead of two.
Core defines this function as the `go` of `List.splitRevAt` for merge sort and does not export it.
`List.splitAt` is optimised for compilation and tail-recursive, but requires a reverse and therefore
two traversals as well. -/
def splitRevAt : List α → ℕ → List α → List α × List α
  | x :: xs, k + 1, acc => splitRevAt xs k (x :: acc)
  | xs, _, acc => (acc, xs)

theorem splitRevAt_eq (l : List α) (k : ℕ) (acc : List α) :
    splitRevAt l k acc = ((l.take k).reverse ++ acc, l.drop k) := by
  induction l generalizing k acc with
  | nil => simp [splitRevAt]
  | cons x xs ih => cases k <;> simp [splitRevAt, ih]

/-- The rows with a nonzero entry at their pivot columns and zeros before it, then the rows
beyond the pivot list (all 0). -/
def IsPivotedList [Zero α] : (cols : List (Fin n)) → (rows : List (List α)) → Prop
  | [], rows => rows = rows.map fun _ ↦ List.replicate n 0 -- one traversal of `rows` only
  | _ :: _, [] => False
  | k :: ks, row :: rows =>
    match splitRevAt row k [] with
    | (_, []) => False
    | (zs, d :: _) => d ≠ 0 ∧ zs = List.replicate k 0 ∧ IsPivotedList ks rows

theorem getD_of_isPivotedList [Zero α] {cols : List (Fin n)} {rows : List (List α)}
    (h : IsPivotedList cols rows) (i : ℕ) :
    (∀ j, (∀ k ∈ cols[i]?, j < (k : ℕ)) → (rows.getD i []).getD j 0 = 0) ∧
      ∀ k ∈ cols[i]?, (rows.getD i []).getD k 0 ≠ 0 := by
  induction cols generalizing rows i with
  | nil =>
    simp only [IsPivotedList, List.map_const'] at h
    grind
  | cons k ks ih =>
    cases rows with
    | nil => simp [IsPivotedList] at h
    | cons row rows =>
      cases i with
      | zero =>
        rw [List.getD_cons_zero]
        have := List.getElem?_drop (xs := row) (i := k) (j := 0)
        refine ⟨fun j hj ↦ ?_, by grind [IsPivotedList, splitRevAt_eq]⟩
        have := List.getElem?_take_of_lt (l := row) (hj k (by simp))
        grind [IsPivotedList, splitRevAt_eq, List.reverse_eq_iff, List.reverse_replicate]
      | succ i => grind [IsPivotedList, splitRevAt_eq, List.getD_cons_succ]

/-- The pivot function of the list of pivot columns: the column of row `i`, and `⊤` for a row
beyond the list. -/
def pivotOfList (m : ℕ) (cols : List (Fin n)) : Fin m → WithTop (Fin n) :=
  fun i ↦ cols[(i : ℕ)]?

theorem pivotOfList_eq_coe {m : ℕ} {cols : List (Fin n)} {i : Fin m} {c : Fin n}
    (hc : cols[(i : ℕ)]? = some c) : pivotOfList m cols i = (c : WithTop (Fin n)) := hc

theorem pivotOfList_lt_pivotOfList {m : ℕ} {cols : List (Fin n)} (hsorted : cols.SortedLT)
    {i j : Fin m} (hij : i < j) (hj : pivotOfList m cols j ≠ ⊤) :
    pivotOfList m cols i < pivotOfList m cols j := by
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hj
  obtain ⟨hjl, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  have hil : (i : ℕ) < cols.length := lt_trans hij hjl
  rw [pivotOfList_eq_coe (List.getElem?_eq_getElem hil), pivotOfList_eq_coe hc]
  exact WithTop.coe_lt_coe.mpr (hsorted.getElem_lt_getElem_of_lt hij)

theorem monotone_pivotOfList_of_sortedLT {m : ℕ} {cols : List (Fin n)}
    (hsorted : cols.SortedLT) : Monotone (pivotOfList m cols) := by
  intro i j hij
  rcases hij.lt_or_eq with hlt | rfl
  · by_cases hj : pivotOfList m cols j = ⊤
    · rw [hj]
      exact le_top
    · exact (pivotOfList_lt_pivotOfList hsorted hlt hj).le
  · exact le_rfl

theorem strictMonoOn_pivotOfList_of_sortedLT {m : ℕ} {cols : List (Fin n)}
    (hsorted : cols.SortedLT) :
    StrictMonoOn (pivotOfList m cols) {i | pivotOfList m cols i ≠ ⊤} :=
  fun _ _ _ hj hij ↦ pivotOfList_lt_pivotOfList hsorted hij hj

theorem isPivotedBy_ofLists [Zero α] {m : ℕ} {rows : List (List α)} {cols : List (Fin n)}
    (hsorted : cols.SortedLT) (h : IsPivotedList cols rows) :
    (ofLists m n rows).IsPivotedBy (pivotOfList m cols) := by
  refine Matrix.isPivotedBy_iff.mpr ⟨monotone_pivotOfList_of_sortedLT hsorted,
    strictMonoOn_pivotOfList_of_sortedLT hsorted, fun i ↦ ?_⟩
  obtain ⟨hzero, hnz⟩ := getD_of_isPivotedList h (i : ℕ)
  simp only [ofLists_apply, ofList_apply]
  refine ⟨fun j hj ↦ hzero (j : ℕ) fun k hk ↦ ?_, fun c hc ↦ ?_⟩
  · rw [pivotOfList_eq_coe hk] at hj
    exact Fin.lt_def.mp (WithTop.coe_lt_coe.mp hj)
  · exact hnz c hc

end Mathlib.Tactic.Echelon
