/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: _
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.CharP.Defs

/-!
TO DO:
- Condense `iUnion_Ioc_subset_Ioc`
- Reorganise `Real.lean` to use this result
-/

open Set

lemma iUnion_Ioc_subset_Ioc {X : Type*} [LinearOrder X] (N : ℕ) (a : ℕ → X) :
    Ioc (a 0) (a N) ⊆ ⋃ i ∈ Finset.range N, Ioc (a i) (a (i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    by_cases hc : a N ≤ a (N + 1)
    · by_cases hc' : a 0 ≤ a N
      · calc
          _ = Ioc (a 0) (a N) ∪ Ioc (a N) (a (N + 1)) := Eq.symm <| Ioc_union_Ioc_eq_Ioc hc' hc
          _ ⊆ (⋃ i ∈ Finset.range N, Ioc (a i) (a (i + 1))) ∪ Ioc (a N) (a (N + 1)) :=
            union_subset_union ih (by rfl)
          _ ⊆ _ := by simp [Finset.mem_insert, Finset.range_succ]
      · push_neg at hc'
        calc
          _ ⊆ Ioc (a N) (a (N + 1)) := by
            refine Ioc_subset_Ioc (le_of_lt hc') (by rfl)
          _ ⊆ _ := by simp [Finset.mem_insert, Finset.range_succ]
    · push_neg at hc
      by_cases hc' : a 0 ≤ a (N + 1)
      · calc
          _ ⊆ Ioc (a 0) (a N) := by simp [← Ioc_union_Ioc_eq_Ioc hc' (le_of_lt hc)]
          _ ⊆ ⋃ i ∈ Finset.range N, Ioc (a i) (a (i + 1)) := ih
          _ ⊆ _ := by simp [Finset.mem_insert, Finset.range_succ]
      · push_neg at hc'
        intro x hx
        have := calc a (N + 1)
          _ < a 0 := hc'
          _ < x := hx.1
          _ ≤ a (N + 1) := hx.2
        exact False.elim <| (lt_self_iff_false _).mp this


lemma iUnion_Ioc_Ioc {X : Type*} [LinearOrderedSemiring X]
    (N : ℕ) (c : X) {δ : X} (hδ : 0 ≤ δ) :
    ⋃ n ∈ Finset.range N, Ioc (c + n * δ) (c + n * δ + δ) = Ioc c (c + N * δ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, Nat.cast_add,
      Nat.cast_one, ih, Finset.range_succ]
    rw [union_comm, Ioc_union_Ioc_eq_Ioc]
    · simp [add_mul, add_assoc]
    · simpa [le_add_iff_nonneg_right] using mul_nonneg (Nat.cast_nonneg' N) hδ
    · simp [hδ]

-- lemma Fin_to_Nat {X : Type*} (N : ℕ) (s : ℕ → Set X) :
--     ⋃ (n : Fin N), s n = ⋃ n ∈ Finset.range N, s n := by
--   ext x
--   simp only [mem_iUnion, Finset.mem_range, exists_prop]
--   constructor
--   · exact fun ⟨i, hi⟩ ↦ ⟨i, i.2, hi⟩
--   · exact fun ⟨i, hiN, hi⟩ ↦ ⟨⟨i, hiN⟩, hi⟩
