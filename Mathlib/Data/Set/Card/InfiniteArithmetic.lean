/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Topology.Instances.ENat.Lemmas

/-!
# More results on cardinalities of sets

This file contain generalizations of lemmas in `Mathlib.Data.Set.Card` to infinite sets.
-/

open Function
variable {ι α : Type*}

namespace Set

lemma encard_biUnion {t : Set ι} {s : ι → Set α} (hs : t.PairwiseDisjoint s) :
    (⋃ i ∈ t, s i).encard = ∑' (i : ι), (t.indicator (fun j ↦ (s j).encard) i) := by
  classical
  let t' : Set ι := { i : ι | i ∈ t ∧ (s i) ≠ ∅ }
  have heq : (⋃ i ∈ t, s i) = (⋃ i ∈ t', s i) := by
    refine subset_antisymm ?_ (Set.biUnion_mono (by simp [t']) (by simp))
    simp_rw [Set.iUnion_subset_iff]
    intro i hi
    by_cases h : (s i) ≠ ∅
    · exact Set.subset_iUnion₂_of_subset i ⟨hi, h⟩ subset_rfl
    · convert Set.empty_subset _
      simpa using h
  obtain (h|h) := Set.finite_or_infinite t'
  · rw [heq, h.encard_biUnion (hs.subset (by simp [t'])), tsum_eq_finsum]
    · refine finsum_congr fun i ↦ ?_
      rw [Set.indicator_apply, finsum_eq_if]
      have (h : s i = ∅) : (s i).encard = 0 := by simpa
      aesop
    · refine h.subset fun i hi ↦ ?_
      simp only [support_indicator, mem_inter_iff, Function.mem_support, ne_eq,
        encard_eq_zero] at hi
      exact ⟨hi.1, hi.2⟩
  · have : (⋃ i ∈ t, s i).Infinite :=
      heq ▸ h.biUnion fun i hi j hj h ↦ hs.elim hi.1 hj.1 (by simp [h, hj.2])
    rw [this.encard_eq, eq_comm, ENat.tsum_eq_top_of_infinite_support]
    apply h.mono
    simp only [ne_eq, support_indicator, subset_inter_iff, sep_subset, true_and, t']
    intro i hi
    simp [hi.2]

lemma encard_iUnion {s : ι → Set α} (hs : Pairwise (Disjoint on s)) :
    (⋃ i, s i).encard = ∑' i, (s i).encard := by
  simp [← biUnion_univ, encard_biUnion (fun a _ b _ hab ↦ hs hab)]

end Set
