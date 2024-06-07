/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring

/-!
# Additive Contents

An additive content `m` on a set of sets `C` is a set function with value 0 at the empty set which
is finitely additive on `C`. That means that for any finset `I` of pairwise disjoint sets in `C`
such that `⋃₀ I ∈ C`, `m (⋃₀ I) = ∑ s ∈ I, m s`.

Mathlib also has a definition of contents over compact sets: see `MeasureTheory.Content`.
A `Content` is in particular an `AddContent` on the set of compact sets.

## Main definitions

* `MeasureTheory.AddContent C`: additive contents over the set of sets `C`.

## Main statements

Let `m` be an `AddContent C`. If `C` is a set semi-ring (`IsSetSemiring C`) we have the properties

* `MeasureTheory.sum_addContent_le_of_subset`: if `I` is a finset of pairwise disjoint sets in `C`
  and `⋃₀ I ⊆ t` for `t ∈ C`, then `∑ s ∈ I, m s ≤ m t`.
* `MeasureTheory.addContent_mono`: if `s ⊆ t` for two sets in `C`, then `m s ≤ m t`.
* `MeasureTheory.addContent_union'`: if `s, t ∈ C` are disjoint and `s ∪ t ∈ C`,
  then `m (s ∪ t) = m s + m t`.
  If `C` is a set ring (`IsSetRing`), then `addContent_union` gives the same conclusion without the
  hypothesis `s ∪ t ∈ C` (since it is a consequence of `IsSetRing C`).

If `C` is a set ring (`MeasureTheory.IsSetRing C`), we have, for `s, t ∈ C`,

* `MeasureTheory.addContent_union_le`: `m (s ∪ t) ≤ m s + m t`
* `MeasureTheory.addContent_le_diff`: `m s - m t ≤ m (s \ t)`

-/

open Set Finset

open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α} {I : Finset (Set α)}

/-- An additive content is a set function with value 0 at the empty set which is finitely additive
on a given set of sets. -/
structure AddContent (C : Set (Set α)) where
  /-- The value of the content on a set. -/
  toFun : Set α → ℝ≥0∞
  empty' : toFun ∅ = 0
  sUnion' (I : Finset (Set α)) (_h_ss : ↑I ⊆ C)
      (_h_dis : PairwiseDisjoint (I : Set (Set α)) id) (_h_mem : ⋃₀ ↑I ∈ C) :
    toFun (⋃₀ I) = ∑ u ∈ I, toFun u

instance : Inhabited (AddContent C) :=
  ⟨{toFun := fun _ => 0
    empty' := by simp
    sUnion' := by simp }⟩

instance : DFunLike (AddContent C) (Set α) (fun _ ↦ ℝ≥0∞) where
  coe := fun m s ↦ m.toFun s
  coe_injective' := by
    intro m m' h
    cases m
    cases m'
    congr

variable {m m' : AddContent C}

@[ext] protected lemma AddContent.ext (h : ∀ s, m s = m' s) : m = m' :=
  DFunLike.ext _ _ h

protected lemma AddContent.ext_iff (m m' : AddContent C) : m = m' ↔ ∀ s, m s = m' s :=
  DFunLike.ext_iff

@[simp] lemma addContent_empty : m ∅ = 0 := m.empty'

lemma addContent_sUnion (h_ss : ↑I ⊆ C)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) (h_mem : ⋃₀ ↑I ∈ C) :
    m (⋃₀ I) = ∑ u ∈ I, m u :=
  m.sUnion' I h_ss h_dis h_mem

lemma addContent_union' (hs : s ∈ C) (ht : t ∈ C) (hst : s ∪ t ∈ C) (h_dis : Disjoint s t) :
    m (s ∪ t) = m s + m t := by
  by_cases hs_empty : s = ∅
  · simp only [hs_empty, Set.empty_union, addContent_empty, zero_add]
  classical
  have h := addContent_sUnion (m := m) (I := {s, t}) ?_ ?_ ?_
  rotate_left
  · simp only [coe_pair, Set.insert_subset_iff, hs, ht, Set.singleton_subset_iff, and_self_iff]
  · simp only [coe_pair, Set.pairwiseDisjoint_insert, pairwiseDisjoint_singleton,
      mem_singleton_iff, Ne, id, forall_eq, true_and_iff]
    exact fun _ => h_dis
  · simp only [coe_pair, sUnion_insert, sUnion_singleton]
    exact hst
  convert h
  · simp only [coe_pair, sUnion_insert, sUnion_singleton]
  · rw [sum_insert, sum_singleton]
    simp only [Finset.mem_singleton]
    refine fun hs_eq_t => hs_empty ?_
    rw [← hs_eq_t] at h_dis
    exact Disjoint.eq_bot_of_self h_dis

section IsSetSemiring

lemma addContent_eq_add_diffFinset₀_of_subset (hC : IsSetSemiring C)
    (hs : s ∈ C) (hI : ↑I ⊆ C) (hI_ss : ∀ t ∈ I, t ⊆ s)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) :
    m s = ∑ i ∈ I, m i + ∑ i ∈ hC.diffFinset₀ hs hI, m i := by
  classical
  conv_lhs => rw [← hC.sUnion_union_diffFinset₀_of_subset hs hI hI_ss]
  rw [addContent_sUnion]
  · rw [sum_union]
    exact hC.disjoint_diffFinset₀ hs hI
  · rw [coe_union]
    exact Set.union_subset hI (hC.diffFinset₀_subset hs hI)
  · rw [coe_union]
    exact hC.pairwiseDisjoint_union_diffFinset₀ hs hI h_dis
  · rwa [hC.sUnion_union_diffFinset₀_of_subset hs hI hI_ss]

lemma sum_addContent_le_of_subset (hC : IsSetSemiring C)
    (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
    (ht : t ∈ C) (hJt : ∀ s ∈ I, s ⊆ t) :
    ∑ u ∈ I, m u ≤ m t := by
  classical
  rw [addContent_eq_add_diffFinset₀_of_subset hC ht h_ss hJt h_dis]
  exact le_add_right le_rfl

lemma addContent_mono (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C)
    (hst : s ⊆ t) :
    m s ≤ m t := by
  have h := sum_addContent_le_of_subset (m := m) hC (I := {s}) ?_ ?_ ht ?_
  · simpa only [sum_singleton] using h
  · rwa [singleton_subset_set_iff]
  · simp only [coe_singleton, pairwiseDisjoint_singleton]
  · simp [hst]

end IsSetSemiring

section IsSetRing

lemma addContent_union (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C)
    (h_dis : Disjoint s t) :
    m (s ∪ t) = m s + m t :=
  addContent_union' hs ht (hC.union_mem hs ht) h_dis

lemma addContent_union_le (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C) :
    m (s ∪ t) ≤ m s + m t := by
  rw [← union_diff_self, addContent_union hC hs (hC.diff_mem ht hs)]
  · exact add_le_add le_rfl
      (addContent_mono hC.isSetSemiring (hC.diff_mem ht hs) ht diff_subset)
  · rw [Set.disjoint_iff_inter_eq_empty, inter_diff_self]

lemma addContent_biUnion_le {ι : Type*} (hC : IsSetRing C) {s : ι → Set α}
    {S : Finset ι} (hs : ∀ n ∈ S, s n ∈ C) :
    m (⋃ i ∈ S, s i) ≤ ∑ i ∈ S, m (s i) := by
  classical
  induction' S using Finset.induction with i S hiS h hs
  · simp
  · rw [Finset.sum_insert hiS]
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    refine (addContent_union_le hC hs.1 (hC.biUnion_mem S hs.2)).trans ?_
    exact add_le_add le_rfl (h hs.2)

lemma le_addContent_diff (m : AddContent C) (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C) :
    m s - m t ≤ m (s \ t) := by
  conv_lhs => rw [← inter_union_diff s t]
  rw [addContent_union hC (hC.inter_mem hs ht) (hC.diff_mem hs ht) disjoint_inf_sdiff, add_comm]
  refine add_tsub_le_assoc.trans_eq ?_
  rw [tsub_eq_zero_of_le
    (addContent_mono hC.isSetSemiring (hC.inter_mem hs ht) ht inter_subset_right), add_zero]

end IsSetRing

end MeasureTheory
