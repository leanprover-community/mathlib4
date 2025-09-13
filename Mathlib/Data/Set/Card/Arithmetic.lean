/-
Copyright (c) 2025 Pim Otte. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Otte
-/

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Results using cardinal arithmetic

This file contains results using cardinal arithmetic that are not in the main cardinal theory files.
It has been separated out to not burden `Mathlib/Data/Set/Card.lean` with extra imports.

## Main results

- `exists_union_disjoint_ncard_eq_of_even`: Given a set `s` with an even cardinality, there exist
  disjoint sets `t` and `u` such that `t ∪ u = s` and `t.ncard = u.ncard`.
- `exists_union_disjoint_cardinal_eq_iff` is the same, except using cardinal notation.
-/

variable {α ι : Type*}

open scoped Finset

theorem Finset.exists_disjoint_union_of_even_card [DecidableEq α] {s : Finset α} (he : Even #s) :
    ∃ (t u : Finset α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u :=
  let ⟨n, hn⟩ := he
  let ⟨t, ht, ht'⟩ := exists_subset_card_eq (show n ≤ #s by omega)
  ⟨t, s \ t, by simp [card_sdiff_of_subset, disjoint_sdiff, *]⟩

theorem Finset.exists_disjoint_union_of_even_card_iff [DecidableEq α] (s : Finset α) :
    Even #s ↔ ∃ (t u : Finset α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u :=
  ⟨Finset.exists_disjoint_union_of_even_card, by
    rintro ⟨t, u, rfl, hdtu, hctu⟩
    simp_all⟩

@[simp]
lemma finsum_one {s : Set α} : ∑ᶠ i ∈ s, 1 = s.ncard := by
  obtain hs | hs := s.infinite_or_finite
  · rw [hs.ncard]
    by_cases h : 1 = 0
    · simp [h]
    · exact finsum_mem_eq_zero_of_infinite (by simpa [Function.support_const h])
  · simp [finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]

namespace Finset

lemma set_ncard_biUnion_le (t : Finset ι) (s : ι → Set α) :
    (⋃ i ∈ t, s i).ncard ≤ ∑ i ∈ t, (s i).ncard :=
  t.apply_union_le_sum (by simp) (Set.ncard_union_le _ _)

lemma set_encard_biUnion_le (t : Finset ι) (s : ι → Set α) :
    (⋃ i ∈ t, s i).encard ≤ ∑ i ∈ t, (s i).encard :=
  t.apply_union_le_sum (by simp) (Set.encard_union_le _ _)

end Finset

namespace Set

variable {s : Set α}

open Cardinal

theorem Infinite.exists_union_disjoint_cardinal_eq_of_infinite (h : s.Infinite) :
    ∃ (t u : Set α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u := by
  have := h.to_subtype
  obtain ⟨f⟩ : Nonempty (s ≃ s ⊕ s) := by
    rw [← Cardinal.eq, ← add_def, add_mk_eq_self]
  refine ⟨Subtype.val '' (f ⁻¹' (range .inl)), Subtype.val '' (f ⁻¹' (range .inr)), ?_, ?_, ?_⟩
  · simp [← image_union, ← preimage_union]
  · exact disjoint_image_of_injective Subtype.val_injective
      (isCompl_range_inl_range_inr.disjoint.preimage f)
  · simp [mk_image_eq Subtype.val_injective]

theorem exists_union_disjoint_cardinal_eq_of_even (he : Even s.ncard) :
    ∃ (t u : Set α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u := by
  obtain hs | hs := s.infinite_or_finite
  · exact hs.exists_union_disjoint_cardinal_eq_of_infinite
  classical
  rw [ncard_eq_toFinset_card s hs] at he
  obtain ⟨t, u, hutu, hdtu, hctu⟩ := Finset.exists_disjoint_union_of_even_card he
  use t.toSet, u.toSet
  simp [← Finset.coe_union, *]

theorem exists_union_disjoint_ncard_eq_of_even (he : Even s.ncard) :
    ∃ (t u : Set α), t ∪ u = s ∧ Disjoint t u ∧ t.ncard = u.ncard := by
  obtain ⟨t, u, hutu, hdtu, hctu⟩ := exists_union_disjoint_cardinal_eq_of_even he
  exact ⟨t, u, hutu, hdtu, congrArg Cardinal.toNat hctu⟩

theorem exists_union_disjoint_cardinal_eq_iff (s : Set α) :
    Even (s.ncard) ↔ ∃ (t u : Set α), t ∪ u = s ∧ Disjoint t u ∧ #t = #u := by
  use exists_union_disjoint_cardinal_eq_of_even
  rintro ⟨t, u, rfl, hdtu, hctu⟩
  obtain hfin | hnfin := (t ∪ u).finite_or_infinite
  · rw [finite_union] at hfin
    have hn : t.ncard = u.ncard := congrArg Cardinal.toNat hctu
    rw [ncard_union_eq hdtu hfin.1 hfin.2, hn]
    exact Even.add_self u.ncard
  · simp [hnfin.ncard]

open scoped Function

lemma Finite.ncard_biUnion {t : Set ι} (ht : t.Finite) {s : ι → Set α} (hs : ∀ i ∈ t, (s i).Finite)
    (h : t.PairwiseDisjoint s) : (⋃ i ∈ t, s i).ncard = ∑ᶠ i ∈ t, (s i).ncard := by
  rw [← finsum_one, finsum_mem_biUnion h ht hs, finsum_mem_congr rfl fun i hi ↦ finsum_one]

lemma ncard_iUnion_of_finite [Finite ι] {s : ι → Set α} (hs : ∀ i, (s i).Finite)
    (h : Pairwise (Disjoint on s)) : (⋃ i, s i).ncard = ∑ᶠ i : ι, (s i).ncard := by
  rw [← finsum_mem_univ, ← finite_univ.ncard_biUnion (by simpa) (fun _ _ _ _ hab ↦ h hab)]
  simp

lemma Finite.encard_biUnion {t : Set ι} (ht : t.Finite) {s : ι → Set α}
    (hs : t.PairwiseDisjoint s) : (⋃ i ∈ t, s i).encard = ∑ᶠ i ∈ t, (s i).encard := by
  classical
  by_cases h : ∀ i ∈ t, (s i).Finite
  · have : (⋃ i ∈ t, s i).Finite := ht.biUnion (fun i hi ↦ h i hi)
    rw [← this.cast_ncard_eq, ncard_biUnion ht h hs,
      ← finsum_mem_congr rfl fun i hi ↦ (h i hi).cast_ncard_eq, Nat.cast_finsum_mem ht]
  · simp only [not_forall] at h
    obtain ⟨i, hi, (hn : (s i).Infinite)⟩ := h
    rw [← Set.insert_diff_self_of_mem hi,
      finsum_mem_insert _ (notMem_diff_of_mem <| mem_singleton i) ht.diff]
    simp [hn]

lemma encard_iUnion_of_finite [Finite ι] {s : ι → Set α} (hs : Pairwise (Disjoint on s)) :
    (⋃ i, s i).encard = ∑ᶠ i, (s i).encard := by
  rw [← finsum_mem_univ, ← finite_univ.encard_biUnion (fun a _ b _ hab ↦ hs hab)]
  simp

lemma Finite.ncard_biUnion_le {t : Set ι} (ht : t.Finite) (s : ι → Set α) :
    (⋃ i ∈ t, s i).ncard ≤ ∑ᶠ i ∈ t, (s i).ncard := by
  simpa [← finsum_mem_eq_finite_toFinset_sum] using ht.toFinset.set_ncard_biUnion_le s

lemma Finite.encard_biUnion_le {t : Set ι} (ht : t.Finite) (s : ι → Set α) :
    (⋃ i ∈ t, s i).encard ≤ ∑ᶠ i ∈ t, (s i).encard := by
  simpa [← finsum_mem_eq_finite_toFinset_sum] using ht.toFinset.set_encard_biUnion_le s

lemma ncard_iUnion_le_of_fintype [Fintype ι] (s : ι → Set α) :
    (⋃ i, s i).ncard ≤ ∑ i, (s i).ncard := by
  simpa using Finset.univ.set_ncard_biUnion_le s

lemma encard_iUnion_le_of_fintype [Fintype ι] (s : ι → Set α) :
    (⋃ i, s i).encard ≤ ∑ i, (s i).encard := by
  simpa using Finset.univ.set_encard_biUnion_le s

lemma ncard_iUnion_le_of_finite [Finite ι] (s : ι → Set α) :
    (⋃ i, s i).ncard ≤ ∑ᶠ i, (s i).ncard := by
  simpa using finite_univ.ncard_biUnion_le s

lemma encard_iUnion_le_of_finite [Finite ι] (s : ι → Set α) :
    (⋃ i, s i).encard ≤ ∑ᶠ i, (s i).encard := by
  simpa using finite_univ.encard_biUnion_le s

end Set
