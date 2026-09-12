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
  grind [List.eq_replicate_of_mem h]

theorem getD_succ (l : List α) (i : ℕ) (d : α) : l.getD (i + 1) d = l.tail.getD i d := by
  simp [List.getD_eq_getElem?_getD]

/-- The first `c` rows from row `k` on, each with a nonzero entry at its diagonal position `k`
followed by zeros to width `n`; a missing row reads as zero and fails. -/
def IsLowerTriangularDiag [Zero α] (n k : ℕ) : ℕ → List (List α) → Prop
  | 0, _ => True
  | c + 1, rows =>
    ((rows.headD []).drop k).headD 0 ≠ 0 ∧
      ((rows.headD []).drop k).tail = List.replicate (n - (k + 1)) 0 ∧
      IsLowerTriangularDiag n (k + 1) c rows.tail

theorem getD_of_isLowerTriangularDiag [Zero α] {n k c i : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiag n k c rows) (hi : i < c) :
    (rows.getD i []).getD (k + i) 0 ≠ 0 ∧ ∀ j, k + i < j → (rows.getD i []).getD j 0 = 0 := by
  induction c generalizing k i rows with
  | zero => simp at hi
  | succ c ih =>
    obtain ⟨hd, hz, hrest⟩ := h
    cases i with
    | zero =>
      rw [← List.headD_eq_getD]
      refine ⟨by simpa using hd, fun j hj ↦ ?_⟩
      have := getD_eq_zero_of_forall_eq_zero (List.eq_replicate_iff.mp hz).2 (j - (k + 1))
      rwa [List.tail_drop, List.getD_eq_getElem?_getD, List.getElem?_drop,
        Nat.add_sub_cancel' (by lia : k + 1 ≤ j), ← List.getD_eq_getElem?_getD] at this
    | succ i =>
      rw [getD_succ, ← Nat.add_assoc, Nat.add_right_comm]
      exact ih hrest (by lia)

theorem isLowerTriangular_ofLists [Zero α] {m : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiag m 0 m rows) : (ofLists m m rows).IsLowerTriangular := by
  intro i j hij
  rw [ofLists_apply, ofList_apply]
  exact (getD_of_isLowerTriangularDiag h i.isLt).2 j (by simpa using hij)

theorem diag_ofLists_ne_zero [Zero α] {m : ℕ} {rows : List (List α)}
    (h : IsLowerTriangularDiag m 0 m rows) (i : Fin m) : (ofLists m m rows).diag i ≠ 0 := by
  rw [Matrix.diag_apply, ofLists_apply, ofList_apply]
  simpa using (getD_of_isLowerTriangularDiag h i.isLt).1

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

/-- The rows with a nonzero entry at their pivot columns and zeros before it, then the rows
beyond the pivot list, all zero. -/
def IsPivotedList [Zero α] (n : ℕ) : List (Fin n) → List (List α) → Prop
  | [], rows => rows = List.replicate rows.length (List.replicate n 0)
  | p :: ps, rows =>
    (rows.headD []).getD p 0 ≠ 0 ∧ (rows.headD []).take p = List.replicate p 0 ∧
      IsPivotedList n ps rows.tail

theorem getD_of_isPivotedList [Zero α] {cols : List (Fin n)} {rows : List (List α)}
    (h : IsPivotedList n cols rows) (i : ℕ) :
    (∀ j : Fin n, (j : WithTop (Fin n)) < (cols[i]?).elim ⊤ (↑) → (rows.getD i []).getD j 0 = 0) ∧
      ∀ c : Fin n, (cols[i]?).elim ⊤ (↑) = (c : WithTop (Fin n)) →
        (rows.getD i []).getD c 0 ≠ 0 := by
  induction cols generalizing rows i with
  | nil =>
    refine ⟨fun j _ ↦ ?_, fun c hc ↦ by simp at hc⟩
    rw [List.getD_eq_getElem?_getD (l := rows)]
    cases hr : rows[i]? with
    | none => rfl
    | some row =>
      rw [Option.getD_some, (List.eq_replicate_iff.mp h).2 row (List.mem_of_getElem? hr)]
      exact getD_eq_zero_of_forall_eq_zero (fun x hx ↦ (List.mem_replicate.mp hx).2) j
  | cons p ps ih =>
    obtain ⟨hd, hz, hrest⟩ := h
    cases i with
    | zero =>
      rw [← List.headD_eq_getD]
      simp only [List.getElem?_cons_zero, Option.elim_some, WithTop.coe_lt_coe, WithTop.coe_eq_coe]
      refine ⟨fun j hj ↦ ?_, fun c hc ↦ hc ▸ hd⟩
      rw [List.getD_eq_getElem?_getD, ← List.getElem?_take_of_lt hj, ← List.getD_eq_getElem?_getD]
      exact getD_eq_zero_of_forall_eq_zero (List.eq_replicate_iff.mp hz).2 j
    | succ i =>
      rw [getD_succ]
      exact ih hrest i

theorem isPivotedBy_ofLists [Zero α] {m : ℕ} {rows : List (List α)} {cols : List (Fin n)}
    (hinc : isStrictlyIncreasing cols = true) (h : IsPivotedList n cols rows) :
    (ofLists m n rows).IsPivotedBy (pivotOfList m cols) := by
  refine Matrix.isPivotedBy_iff.mpr ⟨monotone_pivotOfList_of_isStrictlyIncreasing hinc,
    strictMonoOn_pivotOfList_of_isStrictlyIncreasing hinc, fun i ↦ ?_⟩
  simp only [ofLists_apply, ofList_apply, pivotOfList]
  exact getD_of_isPivotedList h i

end Mathlib.Tactic.Echelon
