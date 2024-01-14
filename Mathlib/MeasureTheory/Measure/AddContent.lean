/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.SetSemiring

/-!
# Additive Contents

An additive content `m` on a set of sets `C` is a set function with value 0 at the empty set which
is finitely additive on `C`. That means that for any finset `I` of pairwise disjoint sets in `C`
such that `⋃₀ I ∈ C`, `m (⋃₀ I) = ∑ s ∈ I, m s`.

Mathlib also has a definition of contents over compact sets: see `MeasureTheory.Content`.
A `Content` is in particular an `AddContent` on the set of compact sets.

TODO: refactor `Content` to use properties of `AddContent`.

## Main definitions

* `MeasureTheory.AddContent C`: additive contents over the set of sets `C`.

## Main statements

Let `m` be an `AddContent C`. If `C` is a set semi-ring (`IsSetSemiring C`) we have the properties

* `MeasureTheory.AddContent.sum_le_of_subset`: if `I` is a finset of pairwise disjoint sets in `C`
  and `⋃₀ I ⊆ t` for `t ∈ C`, then `∑ s in I, m s ≤ m t`.
* `MeasureTheory.AddContent.mono`: if `s ⊆ t` for two sets in `C`, then `m s ≤ m t`.
* `MeasureTheory.AddContent.union'`: if `s, t ∈ C` are disjoint and `s ∪ t ∈ C`,
  then `m (s ∪ t) = m s + m t`.
  If `C` is a set ring (`IsSetRing`), then `AddContent.union` gives the same conclusion without the
  hypothesis `s ∪ t ∈ C` (since it is a consequence of `IsSetRing C`).

If `C` is a set ring (`MeasureTheory.IsSetRing C`), we have, for `s, t ∈ C`,

* `MeasureTheory.AddContent.union_le`: `m (s ∪ t) ≤ m s + m t`
* `MeasureTheory.AddContent.le_sdiff`: `m s - m t ≤ m (s \ t)`

-/

open Set Finset

open scoped ENNReal BigOperators

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α} {I : Finset (Set α)}

/-- An additive content is a set function with value 0 at the empty set which is finitely additive
on a given set of sets. -/
structure AddContent (C : Set (Set α)) where
  /-- The value of the content on a set. -/
  toFun : Set α → ℝ≥0∞
  empty' : toFun ∅ = 0
  add' (I : Finset (Set α)) (_h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (_h_mem : ⋃₀ ↑I ∈ C) :
    toFun (⋃₀ I) = ∑ u in I, toFun u

instance : Inhabited (AddContent C) :=
  ⟨{toFun := fun _ => 0
    empty' := by simp
    add' := by simp }⟩

instance : FunLike (AddContent C) (Set α) (fun _ ↦ ℝ≥0∞) where
  coe := fun m s ↦ m.toFun s
  coe_injective' := by
    intro m m' h
    cases m
    cases m'
    congr

namespace AddContent

@[ext] protected lemma ext {m m' : AddContent C} (h : ∀ s, m s = m' s) : m = m' := by
  refine FunLike.coe_injective ?_
  ext s
  exact h s

protected lemma ext_iff (m m' : AddContent C) : m = m' ↔ ∀ s, m s = m' s :=
  ⟨fun h s ↦ by rw [h], fun h ↦ AddContent.ext h⟩

@[simp] protected lemma empty {m : AddContent C} : m ∅ = 0 := m.empty'

protected lemma add (m : AddContent C) (h_ss : ↑I ⊆ C)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) (h_mem : ⋃₀ ↑I ∈ C) :
    m (⋃₀ I) = ∑ u in I, m u :=
  m.add' I h_ss h_dis h_mem

protected lemma union' (m : AddContent C) (hs : s ∈ C) (ht : t ∈ C) (hst : s ∪ t ∈ C)
    (h_dis : Disjoint s t) :
    m (s ∪ t) = m s + m t := by
  by_cases hs_empty : s = ∅
  · simp only [hs_empty, Set.empty_union, m.empty, zero_add]
  classical
  have h := m.add (I := {s, t}) ?_ ?_ ?_
  rotate_left
  · simp only [coe_pair, Set.insert_subset_iff, hs, ht, Set.singleton_subset_iff, and_self_iff]
  · simp only [coe_pair, Set.pairwiseDisjoint_insert, pairwiseDisjoint_singleton,
      mem_singleton_iff, Ne.def, id.def, forall_eq, true_and_iff]
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

lemma eq_add_diffFinset₀_of_subset (m : AddContent C) (hC : IsSetSemiring C)
    (hs : s ∈ C) (hI : ↑I ⊆ C) (hI_ss : ⋃₀ ↑I ⊆ s)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) :
    m s = ∑ i in I, m i + ∑ i in hC.diffFinset₀ hs hI, m i := by
  classical
  conv_lhs => rw [← hC.sUnion_union_diffFinset₀_of_subset hs hI hI_ss]
  rw [m.add]
  · rw [sum_union]
    exact hC.disjoint_diffFinset₀ hs hI
  · rw [coe_union]
    exact Set.union_subset hI (hC.diffFinset₀_subset hs hI)
  · rw [coe_union]
    exact hC.pairwiseDisjoint_union_diffFinset₀ hs hI h_dis
  · rwa [hC.sUnion_union_diffFinset₀_of_subset hs hI hI_ss]

protected lemma sum_le_of_subset (m : AddContent C) (hC : IsSetSemiring C)
    (h_ss : ↑I ⊆ C) (h_dis : PairwiseDisjoint (I : Set (Set α)) id)
    (ht : t ∈ C) (hJt : ⋃₀ ↑I ⊆ t) :
    ∑ u in I, m u ≤ m t := by
  classical
  rw [m.eq_add_diffFinset₀_of_subset hC ht h_ss hJt h_dis]
  exact le_add_right le_rfl

protected lemma mono (m : AddContent C) (hC : IsSetSemiring C) (hs : s ∈ C) (ht : t ∈ C)
    (hst : s ⊆ t) :
    m s ≤ m t := by
  have h := m.sum_le_of_subset hC (I := {s}) ?_ ?_ ht ?_
  · simpa only [sum_singleton] using h
  · rwa [singleton_subset_set_iff]
  · simp only [coe_singleton, pairwiseDisjoint_singleton]
  · simp only [coe_singleton, sUnion_singleton]
    exact hst

end IsSetSemiring

section IsSetRing

protected lemma union (m : AddContent C) (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C)
    (h_dis : Disjoint s t) :
    m (s ∪ t) = m s + m t :=
  m.union' hs ht (hC.union_mem hs ht) h_dis

protected lemma union_le (m : AddContent C) (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C) :
    m (s ∪ t) ≤ m s + m t := by
  rw [← union_diff_self, m.union hC hs (hC.diff_mem ht hs)]
  · exact add_le_add le_rfl (m.mono hC.isSetSemiring (hC.diff_mem ht hs) ht (diff_subset _ _))
  · rw [Set.disjoint_iff_inter_eq_empty, inter_diff_self]

protected lemma biUnion_le {ι : Type*} (m : AddContent C) (hC : IsSetRing C) {s : ι → Set α}
    {S : Finset ι} (hs : ∀ n ∈ S, s n ∈ C) :
    m (⋃ i ∈ S, s i) ≤ ∑ i in S, m (s i) := by
  classical
  revert hs
  refine Finset.induction ?_ ?_ S
  · simp
  · intro i S hiS h hs
    rw [Finset.sum_insert hiS]
    simp_rw [← Finset.mem_coe, Finset.coe_insert, Set.biUnion_insert]
    simp only [Finset.mem_insert, forall_eq_or_imp] at hs
    refine (m.union_le hC hs.1 (hC.biUnion_mem S hs.2)).trans ?_
    exact add_le_add le_rfl (h hs.2)

protected lemma le_sdiff (m : AddContent C) (hC : IsSetRing C) (hs : s ∈ C) (ht : t ∈ C) :
    m s - m t ≤ m (s \ t) := by
  conv_lhs => rw [← inter_union_diff s t]
  rw [m.union hC (hC.inter_mem hs ht) (hC.diff_mem hs ht) disjoint_inf_sdiff, add_comm]
  refine add_tsub_le_assoc.trans_eq ?_
  rw [tsub_eq_zero_of_le (m.mono hC.isSetSemiring (hC.inter_mem hs ht) ht (inter_subset_right _ _)),
    add_zero]

end IsSetRing

end AddContent

end MeasureTheory
