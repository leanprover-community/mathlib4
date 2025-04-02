/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: _
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Range

/-!
TO DO:
- Find the correct location for these lemmas.
-/

open Set

lemma iUnion_Ioc_subset_Ioc {X : Type*} [LinearOrder X] (N : ℕ) (a : ℕ → X) :
    Ioc (a 0) (a N) ⊆ ⋃ i ∈ Finset.range N, Ioc (a i) (a (i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih => calc
    _ ⊆ Ioc (a 0) (a N) ∪ Ioc (a N) (a (N + 1)) := Ioc_subset_Ioc_union_Ioc
    _ ⊆ _ := by
      simp_rw [Finset.range_succ, Finset.mem_insert, iUnion_iUnion_eq_or_left, union_comm]
      exact union_subset_union_right (Ioc (a N) (a (N + 1))) ih

lemma iUnion_Ico_subset_Ico {X : Type*} [LinearOrder X] (N : ℕ) (a : ℕ → X) :
    Ico (a 0) (a N) ⊆ ⋃ i ∈ Finset.range N, Ico (a i) (a (i + 1)) := by
  induction N with
  | zero => simp
  | succ N ih => calc
    _ ⊆ Ico (a 0) (a N) ∪ Ico (a N) (a (N + 1)) := Ico_subset_Ico_union_Ico
    _ ⊆ _ := by
      simp_rw [Finset.range_succ, Finset.mem_insert, iUnion_iUnion_eq_or_left, union_comm]
      exact union_subset_union_right (Ico (a N) (a (N + 1))) ih

-- lemma iUnion_Ioc_Ioc {X : Type*} [LinearOrderedSemiring X]
--     (N : ℕ) (c : X) {δ : X} (hδ : 0 ≤ δ) :
--     ⋃ n ∈ Finset.range N, Ioc (c + n * δ) (c + n * δ + δ) = Ioc c (c + N * δ) := by
--   induction N with
--   | zero => simp
--   | succ N ih =>
--     simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, Nat.cast_add,
--       Nat.cast_one, ih, Finset.range_succ]
--     rw [union_comm, Ioc_union_Ioc_eq_Ioc]
--     · simp [add_mul, add_assoc]
--     · simpa [le_add_iff_nonneg_right] using mul_nonneg (Nat.cast_nonneg' N) hδ
--     · simp [hδ]

-- lemma Fin_to_Nat {X : Type*} (N : ℕ) (s : ℕ → Set X) :
--     ⋃ (n : Fin N), s n = ⋃ n ∈ Finset.range N, s n := by
--   ext x
--   simp only [mem_iUnion, Finset.mem_range, exists_prop]
--   constructor
--   · exact fun ⟨i, hi⟩ ↦ ⟨i, i.2, hi⟩
--   · exact fun ⟨i, hiN, hi⟩ ↦ ⟨⟨i, hiN⟩, hi⟩
