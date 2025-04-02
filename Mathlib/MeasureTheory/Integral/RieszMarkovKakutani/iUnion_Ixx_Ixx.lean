/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: _
-/
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Range

/-!
TO DO:
- Improve proof of `iUnion_Ioc_subset_Ioc`
- Improve lines 126-137 of `Real.lean` where this result is used
- Add proof of `iUnion_Ico_subset_Ico`
- Add proof of `iUnion_Icc_subset_Icc`
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
      · calc
          _ ⊆ Ioc (a N) (a (N + 1)) := Ioc_subset_Ioc (le_of_lt (not_le.mp hc')) (by rfl)
          _ ⊆ _ := by simp [Finset.mem_insert, Finset.range_succ]
    · by_cases hc' : a 0 ≤ a (N + 1)
      · calc
          _ ⊆ Ioc (a 0) (a N) := by simp [← Ioc_union_Ioc_eq_Ioc hc' (le_of_lt (not_le.mp hc))]
          _ ⊆ ⋃ i ∈ Finset.range N, Ioc (a i) (a (i + 1)) := ih
          _ ⊆ _ := by simp [Finset.mem_insert, Finset.range_succ]
      · intro x hx
        have := calc a (N + 1)
          _ < a 0 := not_le.mp hc'
          _ < x := hx.1
          _ ≤ a (N + 1) := hx.2
        exact False.elim <| (lt_self_iff_false _).mp this

-- lemma iUnion_Ico_subset_Ico {X : Type*} [LinearOrder X] (N : ℕ) (a : ℕ → X) :
--     Ico (a 0) (a N) ⊆ ⋃ i ∈ Finset.range N, Ico (a i) (a (i + 1)) := by sorry

-- lemma iUnion_Icc_subset_Icc {X : Type*} [LinearOrder X] (N : ℕ) (a : ℕ → X) :
--     Icc (a 0) (a N) ⊆ ⋃ i ∈ Finset.range N, Icc (a i) (a (i + 1)) := by sorry


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
