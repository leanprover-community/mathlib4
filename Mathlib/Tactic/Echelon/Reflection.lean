/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Decomposition
public import Mathlib.Tactic.Matrix.OfLists

import Mathlib.Data.List.OfFn

/-!
# Reflection lemmas for the echelon certificate

The conditions of `Echelon.Decomposition` on a matrix given as a list of rows, each stated as a
sweep along the rows that the kernel evaluates, with a bridge lemma to the condition on `ofLists`.

## Main definitions

- `PivotStep`
- `aboveDiagonal`, `diag`
- `pivotPrefixes`, `pivotEntries`

## Main results

- `isChain_ofFn_iff_monotone_and_strictMonoOn`
- `isLowerTriangular_ofLists`
- `diag_ofLists_ne_zero`
- `isPivotedBy_ofLists`

## Implementation notes

The kernel has no random access into a list: reading the entry at position `k` walks `k` cells.
Each condition is therefore a sweep whose recursion mirrors the list constructors and reads each
row once, and two conditions that need entries at the same position take them from the same
suffix of the row, which the kernel computes once.

A zero condition is closed by one equation between the collected entries and a replicated zero,
which the kernel decides by evaluation. A nonzero condition takes the collected entries as a
list, so that proofs of the individual entries can be attached along it.
-/

@[expose] public section

open Mathlib.Tactic.Matrix

namespace Mathlib.Tactic.Echelon

/-! ### The pivot-function conditions in chain form

The pivot certificates defined in the theory file using `Monotone` and `StrictMonoOn` have
decidable instances but require `O(n^2)` comparisons, since they use the general decidable
instances from `Monotone` which check all pairs. The following part defines a `List.isChain`-based
alternative that can be decided in `O(n) comparisons`.
-/

section PivotChain

variable {α : Type*} [Top α]

/-- One step of a pivot function: strictly increasing, with `⊤` absorbing. -/
def PivotStep [LT α] (a b : α) : Prop :=
  a < b ∨ a = ⊤ ∧ b = ⊤

instance [Preorder α] : IsTrans α PivotStep where
  trans a b c h₁ h₂ := by
    simp only [PivotStep] at *
    grind

instance [LT α] [i : ∀ a b : α, Decidable (a < b ∨ a = ⊤ ∧ b = ⊤)] :
    DecidableRel (PivotStep (α := α)) := i

/-- TODO: List.ofFn still brings up a O(n^2) construction. This can be improved by using a
list bridge eventually. -/
theorem isChain_ofFn_iff_monotone_and_strictMonoOn [PartialOrder α] {m : ℕ} (l : Fin m → α) :
    (List.ofFn l).IsChain PivotStep ↔ Monotone l ∧ StrictMonoOn l {i | l i ≠ ⊤} := by
  rw [List.isChain_iff_pairwise, List.pairwise_ofFn]
  simp only [PivotStep, Monotone, StrictMonoOn]
  grind [le_of_lt, LE.le.eq_or_lt]

end PivotChain

/-! ### The entry conditions as row sweeps -/

variable {R : Type*}

/-- The entries above the diagonal of a list of rows, row `k` contributing its entries after
position `k`, collected row by row. -/
def aboveDiagonal (k : Nat) : List (List R) → List R
  | [] => []
  | row :: rows => (row.drop k).tail ++ aboveDiagonal (k + 1) rows

theorem getD_eq_zero_of_aboveDiagonal [Zero R] {k i j : Nat} {rows : List (List R)}
    (h : ∀ x ∈ aboveDiagonal k rows, x = 0) (hij : k + i < j) :
    (rows.getD i []).getD j 0 = 0 := by
  induction rows generalizing k i with
  | nil => simp
  | cons row rows ih =>
    simp only [aboveDiagonal, List.tail_drop, List.mem_append] at h
    cases i with
    | zero =>
      obtain ⟨d, rfl⟩ : ∃ d, j = (k + 1) + d := ⟨j - (k + 1), by lia⟩
      rw [List.getD_cons_zero, List.getD_eq_getElem?_getD, ← List.getElem?_drop]
      cases hx : (row.drop (k + 1))[d]? with
      | none => rfl
      | some x => exact h x (Or.inl (List.mem_of_getElem? hx))
    | succ i =>
      rw [List.getD_cons_succ]
      exact ih (fun x hx => h x (Or.inr hx)) (by lia)

theorem isLowerTriangular_ofLists [Zero R] {m : ℕ} {rows : List (List R)} {N : ℕ}
    (h : aboveDiagonal 0 rows = List.replicate N 0) : (ofLists m m rows).IsLowerTriangular := by
  intro i j hij
  rw [ofLists_apply, ofList_apply]
  exact getD_eq_zero_of_aboveDiagonal (List.eq_replicate_iff.mp h).2 (by simpa using hij)

/-- The first `c` diagonal entries of a list of rows, row `k` contributing its entry at
position `k`, with missing rows and entries read as `0`. The entry is read from the same
`row.drop k` as `aboveDiagonal`, which the kernel then computes once for both. -/
def diag [Zero R] (k : Nat) : Nat → List (List R) → List R
  | 0, _ => []
  | c + 1, rows => ((rows.headD []).drop k).headD 0 :: diag (k + 1) c rows.tail

theorem getD_ne_zero_of_diag [Zero R] {k c i : Nat} {rows : List (List R)}
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
      rw [List.getD_eq_getElem?_getD (l := rows), ← List.getElem?_tail,
        ← List.getD_eq_getElem?_getD, ← Nat.add_assoc, Nat.add_right_comm]
      exact ih h.2 (by lia)

theorem diag_ofLists_ne_zero [Zero R] {m : ℕ} {rows : List (List R)}
    (h : ∀ x ∈ diag 0 m rows, x ≠ 0) (i : Fin m) : (ofLists m m rows).diag i ≠ 0 := by
  rw [Matrix.diag_apply, ofLists_apply, ofList_apply]
  simpa using getD_ne_zero_of_diag h i.isLt

variable {n : ℕ}

/-- The entries of each row before its pivot column, collected row by row; a row whose pivot
is `⊤` contributes all its entries. -/
def pivotPrefixes : List (WithTop (Fin n)) → List (List R) → List R
  | [], _ => []
  | (p : Fin n) :: ps, rows => (rows.headD []).take p ++ pivotPrefixes ps rows.tail
  | none :: ps, rows => rows.headD [] ++ pivotPrefixes ps rows.tail

/-- The entry of each row at its pivot column, for the rows whose pivot is a column. -/
def pivotEntries [Zero R] : List (WithTop (Fin n)) → List (List R) → List R
  | [], _ => []
  | (p : Fin n) :: ps, rows => (rows.headD []).getD p 0 :: pivotEntries ps rows.tail
  | none :: ps, rows => pivotEntries ps rows.tail

theorem getD_eq_zero_of_pivotPrefixes [Zero R] {ps : List (WithTop (Fin n))}
    {rows : List (List R)} (h : ∀ x ∈ pivotPrefixes ps rows, x = 0) {i : ℕ} {j : Fin n}
    (hi : i < ps.length) (hj : (j : WithTop (Fin n)) < ps.getD i ⊤) :
    (rows.getD i []).getD j 0 = 0 := by
  induction ps generalizing rows i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero =>
      rw [← List.headD_eq_getD, List.getD_eq_getElem?_getD]
      cases p with
      | coe q =>
        simp only [List.getD_cons_zero, WithTop.coe_lt_coe] at hj
        simp only [pivotPrefixes, List.mem_append] at h
        rw [← List.getElem?_take_of_lt hj]
        cases hx : ((rows.headD []).take q)[j]? with
        | none => rfl
        | some x => exact h x (Or.inl (List.mem_of_getElem? hx))
      | top =>
        simp only [pivotPrefixes, List.mem_append] at h
        cases hx : (rows.headD [])[j]? with
        | none => rfl
        | some x => exact h x (Or.inl (List.mem_of_getElem? hx))
    | succ i =>
      rw [List.getD_eq_getElem?_getD (l := rows), ← List.getElem?_tail,
        ← List.getD_eq_getElem?_getD]
      cases p with
      | coe q =>
        simp only [pivotPrefixes, List.mem_append] at h
        exact ih (fun x hx => h x (Or.inr hx)) (by simpa using hi) hj
      | top =>
        simp only [pivotPrefixes, List.mem_append] at h
        exact ih (fun x hx => h x (Or.inr hx)) (by simpa using hi) hj

theorem getD_ne_zero_of_pivotEntries [Zero R] {ps : List (WithTop (Fin n))}
    {rows : List (List R)} (h : ∀ x ∈ pivotEntries ps rows, x ≠ 0) {i : ℕ} {c : Fin n}
    (hc : ps.getD i ⊤ = c) : (rows.getD i []).getD c 0 ≠ 0 := by
  induction ps generalizing rows i with
  | nil => simp at hc
  | cons p ps ih =>
    cases i with
    | zero =>
      rw [List.getD_cons_zero] at hc
      subst hc
      rw [← List.headD_eq_getD]
      exact h _ (List.mem_cons_self ..)
    | succ i =>
      rw [List.getD_eq_getElem?_getD (l := rows), ← List.getElem?_tail,
        ← List.getD_eq_getElem?_getD]
      cases p with
      | coe q => exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) hc
      | top => exact ih h hc

theorem isPivotedBy_ofLists [Zero R] {m : ℕ} {rows : List (List R)}
    {pivot : Fin m → WithTop (Fin n)} {ps : List (WithTop (Fin n))} (hps : List.ofFn pivot = ps)
    (hchain : ps.IsChain PivotStep) {N : ℕ} (hzero : pivotPrefixes ps rows = List.replicate N 0)
    (hnz : ∀ x ∈ pivotEntries ps rows, x ≠ 0) : (ofLists m n rows).IsPivotedBy pivot := by
  have hmono := (isChain_ofFn_iff_monotone_and_strictMonoOn pivot).mp (hps ▸ hchain)
  refine Matrix.isPivotedBy_iff.mpr ⟨hmono.1, hmono.2, fun i => ?_⟩
  have hi : ps.getD i ⊤ = pivot i := by simp [← hps]
  refine ⟨fun j hj => ?_, fun c hc => ?_⟩
  · rw [ofLists_apply, ofList_apply]
    exact getD_eq_zero_of_pivotPrefixes (List.eq_replicate_iff.mp hzero).2 (by simp [← hps])
      (hi ▸ hj)
  · rw [ofLists_apply, ofList_apply]
    exact getD_ne_zero_of_pivotEntries hnz (hi.trans hc)

end Mathlib.Tactic.Echelon
