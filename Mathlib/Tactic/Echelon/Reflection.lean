/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot
public import Mathlib.Tactic.Matrix.OfLists

/-!
# Reflection lemmas for the echelon certificate

The conditions of `Echelon.Decomposition` on a matrix given as a list of rows, each a sweep along
the rows, with a bridge lemma to the condition on `ofLists`.
-/

@[expose] public section

open Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Echelon

variable {α : Type*}

theorem getD_eq_zero_of_forall_eq_zero [Zero α] {l : List α} (h : ∀ x ∈ l, x = 0) (i : ℕ) :
    l.getD i 0 = 0 := by
  rw [List.eq_replicate_of_mem h]
  grind

theorem getD_succ (l : List α) (i : ℕ) (d : α) : l.getD (i + 1) d = l.tail.getD i d := by
  simp [List.getD_eq_getElem?_getD]

/-- The entries above the diagonal of a list of rows, collected row by row. -/
def aboveDiagonal (k : Nat) : List (List α) → List α
  | [] => []
  | row :: rows => (row.drop k).tail ++ aboveDiagonal (k + 1) rows

theorem getD_eq_zero_of_aboveDiagonal [Zero α] {k i j : Nat} {rows : List (List α)}
    (h : ∀ x ∈ aboveDiagonal k rows, x = 0) (hij : k + i < j) :
    (rows.getD i []).getD j 0 = 0 := by
  induction rows generalizing k i with
  | nil => simp
  | cons row rows ih =>
    simp only [aboveDiagonal, List.tail_drop, List.mem_append] at h
    cases i with
    | zero =>
      have := getD_eq_zero_of_forall_eq_zero (fun x hx ↦ h x (Or.inl hx)) (j - (k + 1))
      rw [List.getD_cons_zero]
      rwa [List.getD_eq_getElem?_getD, List.getElem?_drop,
        Nat.add_sub_cancel' (by lia : k + 1 ≤ j), ← List.getD_eq_getElem?_getD] at this
    | succ i =>
      rw [List.getD_cons_succ]
      exact ih (fun x hx ↦ h x (Or.inr hx)) (by lia)

theorem isLowerTriangular_ofLists [Zero α] {m : ℕ} {rows : List (List α)} {N : ℕ}
    (h : aboveDiagonal 0 rows = List.replicate N 0) : (ofLists m m rows).IsLowerTriangular := by
  intro i j hij
  rw [ofLists_apply, ofList_apply]
  exact getD_eq_zero_of_aboveDiagonal (List.eq_replicate_iff.mp h).2 (by simpa using hij)

/-- The first `c` diagonal entries of a list of rows, missing ones read as `0`, taken from the
`row.drop k` that `aboveDiagonal` also reads. -/
def diag [Zero α] (k : Nat) : Nat → List (List α) → List α
  | 0, _ => []
  | c + 1, rows => ((rows.headD []).drop k).headD 0 :: diag (k + 1) c rows.tail

theorem getD_ne_zero_of_diag [Zero α] {k c i : Nat} {rows : List (List α)}
    (h : ∀ x ∈ diag k c rows, x ≠ 0) (hi : i < c) : (rows.getD i []).getD (k + i) 0 ≠ 0 := by
  induction c generalizing k i rows with
  | zero => simp at hi
  | succ c ih =>
    simp only [diag, List.forall_mem_cons] at h
    cases i with
    | zero =>
      rw [← List.headD_eq_getD]
      simpa using h.1
    | succ i =>
      rw [getD_succ, ← Nat.add_assoc, Nat.add_right_comm]
      exact ih h.2 (by lia)

theorem diag_ofLists_ne_zero [Zero α] {m : ℕ} {rows : List (List α)}
    (h : ∀ x ∈ diag 0 m rows, x ≠ 0) (i : Fin m) : (ofLists m m rows).diag i ≠ 0 := by
  rw [Matrix.diag_apply, ofLists_apply, ofList_apply]
  simpa using getD_ne_zero_of_diag h i.isLt

variable {n : ℕ}

/-- The pivot function of the list of pivot columns, `⊤` for the rows beyond the list. -/
def pivotOfList (m : ℕ) (cols : List (Fin n)) : Fin m → WithTop (Fin n) :=
  fun i ↦ (cols[(i : ℕ)]?).elim ⊤ (↑)

theorem pivotOfList_eq_top_iff {m : ℕ} {cols : List (Fin n)} {i : Fin m} :
    pivotOfList m cols i = ⊤ ↔ cols.length ≤ i := by
  cases h : cols[(i : ℕ)]? <;> simp [pivotOfList, h] <;> grind

/-- `true` when the list is strictly increasing. -/
def isStrictlyIncreasing : List (Fin n) → Bool
  | a :: b :: l => Nat.blt a b && isStrictlyIncreasing (b :: l)
  | _ => true

theorem isStrictlyIncreasing_iff_isChain :
    ∀ {l : List (Fin n)}, isStrictlyIncreasing l = true ↔ l.IsChain (· < ·)
  | [] => by simp [isStrictlyIncreasing]
  | [_] => by simp [isStrictlyIncreasing]
  | _ :: b :: l => by
    simp [isStrictlyIncreasing, List.isChain_cons_cons, Nat.blt_eq,
      isStrictlyIncreasing_iff_isChain (l := b :: l)]

theorem pivotOfList_lt_pivotOfList {m : ℕ} {cols : List (Fin n)}
    (h : isStrictlyIncreasing cols = true) {i j : Fin m} (hij : i < j)
    (hj : (j : ℕ) < cols.length) : pivotOfList m cols i < pivotOfList m cols j := by
  rw [isStrictlyIncreasing_iff_isChain, List.isChain_iff_pairwise, List.pairwise_iff_getElem] at h
  have hi : (i : ℕ) < cols.length := lt_trans hij hj
  simp only [pivotOfList, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.elim_some]
  exact WithTop.coe_lt_coe.mpr (h i j hi hj hij)

theorem monotone_pivotOfList_of_isStrictlyIncreasing {m : ℕ} {cols : List (Fin n)}
    (h : isStrictlyIncreasing cols = true) : Monotone (pivotOfList m cols) := by
  intro i j hij
  rcases hij.lt_or_eq with hlt | rfl
  · by_cases hj : (j : ℕ) < cols.length
    · exact (pivotOfList_lt_pivotOfList h hlt hj).le
    · rw [pivotOfList_eq_top_iff.mpr (not_lt.mp hj)]
      exact le_top
  · exact le_rfl

theorem strictMonoOn_pivotOfList_of_isStrictlyIncreasing {m : ℕ} {cols : List (Fin n)}
    (h : isStrictlyIncreasing cols = true) :
    StrictMonoOn (pivotOfList m cols) {i | pivotOfList m cols i ≠ ⊤} :=
  fun _ _ _ hj hij ↦
    pivotOfList_lt_pivotOfList h hij (lt_of_not_ge (mt pivotOfList_eq_top_iff.mpr hj))

/-- The entries of each row before its pivot column, and all of the rows beyond the pivot
list. -/
def pivotPrefixes : List (Fin n) → List (List α) → List α
  | [], rows => rows.flatten
  | p :: ps, rows => (rows.headD []).take p ++ pivotPrefixes ps rows.tail

/-- The entries of the rows at their pivot columns. -/
def pivotEntries [Zero α] : List (Fin n) → List (List α) → List α
  | [], _ => []
  | p :: ps, rows => (rows.headD []).getD p 0 :: pivotEntries ps rows.tail

theorem getD_eq_zero_of_pivotPrefixes [Zero α] {cols : List (Fin n)} {rows : List (List α)}
    (h : ∀ x ∈ pivotPrefixes cols rows, x = 0) {i : ℕ} {j : Fin n}
    (hj : (j : WithTop (Fin n)) < (cols[i]?).elim ⊤ (↑)) : (rows.getD i []).getD j 0 = 0 := by
  induction cols generalizing rows i with
  | nil =>
    refine getD_eq_zero_of_forall_eq_zero (fun x hx ↦ h x ?_) j
    simp only [pivotPrefixes, List.mem_flatten]
    rw [List.getD_eq_getElem?_getD] at hx
    cases hrow : rows[i]? with
    | none => simp [hrow] at hx
    | some row => exact ⟨row, List.mem_of_getElem? hrow, by simpa [hrow] using hx⟩
  | cons p ps ih =>
    simp only [pivotPrefixes, List.mem_append] at h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.elim_some, WithTop.coe_lt_coe] at hj
      rw [← List.headD_eq_getD, List.getD_eq_getElem?_getD, ← List.getElem?_take_of_lt hj,
        ← List.getD_eq_getElem?_getD]
      exact getD_eq_zero_of_forall_eq_zero (fun x hx ↦ h x (Or.inl hx)) j
    | succ i =>
      rw [getD_succ]
      exact ih (fun x hx ↦ h x (Or.inr hx)) hj

theorem getD_ne_zero_of_pivotEntries [Zero α] {cols : List (Fin n)} {rows : List (List α)}
    (h : ∀ x ∈ pivotEntries cols rows, x ≠ 0) {i : ℕ} {c : Fin n}
    (hc : (cols[i]?).elim ⊤ (↑) = (c : WithTop (Fin n))) : (rows.getD i []).getD c 0 ≠ 0 := by
  induction cols generalizing rows i with
  | nil => simp at hc
  | cons p ps ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.elim_some, WithTop.coe_eq_coe] at hc
      subst hc
      rw [← List.headD_eq_getD]
      exact h _ (List.mem_cons_self ..)
    | succ i =>
      rw [getD_succ]
      exact ih (fun x hx ↦ h x (List.mem_cons_of_mem _ hx)) hc

theorem isPivotedBy_ofLists [Zero α] {m : ℕ} {rows : List (List α)} {cols : List (Fin n)}
    (hinc : isStrictlyIncreasing cols = true) {N : ℕ}
    (hzero : pivotPrefixes cols rows = List.replicate N 0)
    (hnz : ∀ x ∈ pivotEntries cols rows, x ≠ 0) :
    (ofLists m n rows).IsPivotedBy (pivotOfList m cols) := by
  refine Matrix.isPivotedBy_iff.mpr ⟨monotone_pivotOfList_of_isStrictlyIncreasing hinc,
    strictMonoOn_pivotOfList_of_isStrictlyIncreasing hinc, fun i ↦ ?_⟩
  constructor
  · intro j hj
    rw [ofLists_apply, ofList_apply]
    exact getD_eq_zero_of_pivotPrefixes (List.eq_replicate_iff.mp hzero).2 hj
  · intro c hc
    rw [ofLists_apply, ofList_apply]
    exact getD_ne_zero_of_pivotEntries hnz hc

end Mathlib.Tactic.Echelon
