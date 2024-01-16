/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Instances.ENNReal

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

### σ-additive and σ-subadditive contents

We say that an additive content `m` is σ-additive on `C` if for all sequences of pairwise disjoints
sets `s : ℕ → Set α` in `C`, `m (⋃ i, s i) = ∑' i, m (s i)`.
We say that an additive content is σ-subadditive on `C` if for all sequences of sets of `C` (not
necessarily disjoint) `s : ℕ → Set α`, `m (⋃ i, s i) ≤ ∑' i, m (s i)`.

* `AddContent.iUnion_eq_tsum_of_disjoint_of_iUnion_le`: if an `AddContent` is σ-subadditive on
  a semi-ring of sets, then it is σ-additive.
* `AddContent.iUnion_le_of_iUnion_eq_tsum`: if an `AddContent` is σ-additive on a ring of sets,
  then it is σ-subadditive.

* `AddContent.tendsto_atTop_iUnion_of_iUnion_eq_tsum`: if an additive content is σ-additive on a
  ring of sets, then the content of a monotone sequence of sets tends to the content of the union.

-/

open Set Finset Filter

open scoped ENNReal BigOperators Topology

namespace MeasureTheory

variable {α : Type*} {C : Set (Set α)} {s t : Set α} {I : Finset (Set α)}

/-- An additive content is a set function with value 0 at the empty set which is finitely additive
on a given set of sets. -/
structure AddContent (C : Set (Set α)) where
  /-- The value of the content on a set. -/
  toFun : Set α → ℝ≥0∞
  empty' : toFun ∅ = 0
  sUnion_eq_sum' (I : Finset (Set α)) (_h_ss : ↑I ⊆ C)
      (_h_dis : PairwiseDisjoint (I : Set (Set α)) id) (_h_mem : ⋃₀ ↑I ∈ C) :
    toFun (⋃₀ I) = ∑ u in I, toFun u

instance : Inhabited (AddContent C) :=
  ⟨{toFun := fun _ ↦ 0
    empty' := by simp
    sUnion_eq_sum' := by simp }⟩

instance : FunLike (AddContent C) (Set α) (fun _ ↦ ℝ≥0∞) where
  coe := fun m s ↦ m.toFun s
  coe_injective' := by
    intro m m' h
    cases m
    cases m'
    congr

namespace AddContent

@[ext] protected lemma ext {m m' : AddContent C} (h : ∀ s, m s = m' s) : m = m' := FunLike.ext _ _ h

protected lemma ext_iff (m m' : AddContent C) : m = m' ↔ ∀ s, m s = m' s := FunLike.ext_iff

@[simp] protected lemma apply_empty {m : AddContent C} : m ∅ = 0 := m.empty'

protected lemma sUnion_eq_sum (m : AddContent C) (h_ss : ↑I ⊆ C)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) (h_mem : ⋃₀ ↑I ∈ C) :
    m (⋃₀ I) = ∑ u in I, m u :=
  m.sUnion_eq_sum' I h_ss h_dis h_mem

protected lemma union' (m : AddContent C) (hs : s ∈ C) (ht : t ∈ C) (hst : s ∪ t ∈ C)
    (h_dis : Disjoint s t) :
    m (s ∪ t) = m s + m t := by
  by_cases hs_empty : s = ∅
  · simp only [hs_empty, Set.empty_union, m.apply_empty, zero_add]
  classical
  have h := m.sUnion_eq_sum (I := {s, t}) ?_ ?_ ?_
  rotate_left
  · simp only [coe_pair, Set.insert_subset_iff, hs, ht, Set.singleton_subset_iff, and_self_iff]
  · simp only [coe_pair, Set.pairwiseDisjoint_insert, pairwiseDisjoint_singleton,
      mem_singleton_iff, Ne.def, id.def, forall_eq, true_and_iff]
    exact fun _ ↦ h_dis
  · simp only [coe_pair, sUnion_insert, sUnion_singleton]
    exact hst
  convert h
  · simp only [coe_pair, sUnion_insert, sUnion_singleton]
  · rw [sum_insert, sum_singleton]
    simp only [Finset.mem_singleton]
    refine fun hs_eq_t ↦ hs_empty ?_
    rw [← hs_eq_t] at h_dis
    exact Disjoint.eq_bot_of_self h_dis

section IsSetSemiring

lemma eq_add_diffFinset₀_of_subset (m : AddContent C) (hC : IsSetSemiring C)
    (hs : s ∈ C) (hI : ↑I ⊆ C) (hI_ss : ⋃₀ ↑I ⊆ s)
    (h_dis : PairwiseDisjoint (I : Set (Set α)) id) :
    m s = ∑ i in I, m i + ∑ i in hC.diffFinset₀ hs hI, m i := by
  classical
  conv_lhs => rw [← hC.sUnion_union_diffFinset₀_of_subset hs hI hI_ss]
  rw [m.sUnion_eq_sum]
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

lemma sUnion_le_sum (m : AddContent C) (hC : IsSetSemiring C)
    (J : Finset (Set α)) (h_ss : ↑J ⊆ C) (h_mem : ⋃₀ ↑J ∈ C) :
    m (⋃₀ ↑J) ≤ ∑ u in J, m u := by
  classical
  rw [← hC.sUnion_allDiffFinset₀ J h_ss, m.add]
  rotate_left
  · exact hC.allDiffFinset₀_subset J h_ss
  · exact hC.pairwiseDisjoint_allDiffFinset₀ J h_ss
  · rwa [hC.sUnion_allDiffFinset₀ J h_ss]
  rw [IsSetSemiring.allDiffFinset₀, sum_disjiUnion, ← sum_ordered J]
  refine sum_le_sum fun i _ ↦ m.sum_le_of_subset hC ?_ ?_ ?_ ?_
  · exact hC.indexedDiffFinset₀_subset J h_ss i
  · exact hC.pairwiseDisjoint_indexedDiffFinset₀' J h_ss i
  · exact ordered_mem' h_ss i
  · exact hC.sUnion_indexedDiffFinset₀_subset J h_ss i

lemma le_sum_of_subset_sUnion (m : AddContent C) (hC : IsSetSemiring C)
    (J : Finset (Set α)) (h_ss : ↑J ⊆ C) (ht : t ∈ C) (htJ : t ⊆ ⋃₀ ↑J) :
    m t ≤ ∑ u in J, m u := by
  classical
  let Jt := Finset.image (fun u ↦ t ∩ u) J
  have ht_eq : t = ⋃₀ Jt := by
    rw [coe_image, sUnion_image, ← inter_iUnion₂, inter_eq_self_of_subset_left]
    rwa [← sUnion_eq_biUnion]
  rw [ht_eq]
  refine' (m.sUnion_le_sum hC Jt _ _).trans _
  · intro s
    simp only [coe_image, Set.mem_image, mem_coe, forall_exists_index, and_imp]
    rintro u hu rfl
    exact hC.inter_mem _ ht _ (h_ss hu)
  · rwa [← ht_eq]
  refine (Finset.sum_image_le J _ m fun _ _ ↦ zero_le _).trans ?_
  refine sum_le_sum fun u hu ↦ ?_
  exact m.mono hC (hC.inter_mem _ ht _ (h_ss hu)) (h_ss hu) (inter_subset_right _ _)

/-- If an `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additive. -/
theorem iUnion_eq_tsum_of_disjoint_of_iUnion_le (m : AddContent C) (hC : IsSetSemiring C)
    (m_subadd : ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : ⋃ i, f i ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) ≤ ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
    (hf_disj : Pairwise (Disjoint on f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  refine le_antisymm (m_subadd f hf hf_Union hf_disj) ?_
  refine tsum_le_of_sum_le ENNReal.summable fun I ↦ ?_
  classical
  rw [← Finset.sum_image_of_disjoint m m.empty f _ (hf_disj.pairwiseDisjoint _)]
  refine m.sum_le_of_subset hC (I := I.image f) ?_ ?_ ?_ ?_
  · simp only [coe_image, Set.image_subset_iff]
    refine (subset_preimage_image f I).trans (preimage_mono ?_)
    rintro i ⟨j, _, rfl⟩
    exact hf j
  · simp only [coe_image]
    intro s hs t ht hst
    rw [Set.mem_image] at hs ht
    obtain ⟨i, _, rfl⟩ := hs
    obtain ⟨j, _, rfl⟩ := ht
    have hij : i ≠ j := by intro h_eq; rw [h_eq] at hst; exact hst rfl
    exact hf_disj hij
  · exact hf_Union
  · simp only [coe_image, sUnion_image, mem_coe, iUnion_subset_iff]
    exact fun i _ ↦ subset_iUnion _ i

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

/-- If an additive content is σ-additive on a set ring, then the content of a monotone sequence of
sets tends to the content of the union. -/
theorem tendsto_atTop_iUnion_of_iUnion_eq_tsum (m : AddContent C) (hC : IsSetRing C)
    (m_add : ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
        (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    (f : ℕ → Set α) (hf_mono : Monotone f) (hf : ∀ i, f i ∈ C) (hf_Union : ⋃ i, f i ∈ C) :
    Tendsto (fun n ↦ m (f n)) atTop (𝓝 (m (⋃ i, f i))) := by
  classical
  let g := disjointed f
  have hg_Union : (⋃ i, g i) = ⋃ i, f i := iUnion_disjointed
  specialize m_add g (hC.disjointed_mem hf) _ (disjoint_disjointed f)
  · rwa [hg_Union]
  rw [← hg_Union]
  simp_rw [m_add]
  have h : ∀ n, m (f n) = ∑ i in range (n + 1), m (g i) := by
    intro n
    have h1 : f n = ⋃₀ Finset.image g (range (n + 1)) := by
      rw [← Monotone.partialSups_eq hf_mono, ← partialSups_disjointed, ←
        partialSups_eq_sUnion_image g]
    rw [h1, m.add]
    rotate_left
    · intro s
      rw [mem_coe, Finset.mem_image]
      rintro ⟨i, _, rfl⟩
      exact hC.disjointed_mem hf i
    · intro s hs t ht hst
      rw [mem_coe, Finset.mem_image] at hs ht
      obtain ⟨i, _, rfl⟩ := hs
      obtain ⟨j, _, rfl⟩ := ht
      have hij : i ≠ j := by intro h_eq; rw [h_eq] at hst; exact hst rfl
      exact disjoint_disjointed f hij
    · rw [← h1]; exact hf n
    rw [sum_image_of_disjoint m m.empty g _ ((disjoint_disjointed f).pairwiseDisjoint _)]
  simp_rw [h]
  change Tendsto (fun n ↦ (fun k ↦ ∑ i in range k, m (g i)) (n + 1)) atTop (𝓝 (∑' i, m (g i)))
  rw [tendsto_add_atTop_iff_nat (f := (fun k ↦ ∑ i in range k, m (g i))) 1]
  exact ENNReal.tendsto_nat_tsum _

/-- If an additive content is σ-additive on a set ring, then it is σ-subadditive. -/
theorem iUnion_le_of_iUnion_eq_tsum (m : AddContent C) (hC : IsSetRing C)
    (m_add : ∀ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
      (_hf_disj : Pairwise (Disjoint on f)), m (⋃ i, f i) = ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : ⋃ i, f i ∈ C) :
    m (⋃ i, f i) ≤ ∑' i, m (f i) := by
  classical
  have h_tendsto : Tendsto (fun n ↦ m (partialSups f n)) atTop (𝓝 (m (⋃ i, f i))) := by
    rw [← iSup_eq_iUnion, ← iSup_partialSups_eq]
    refine m.tendsto_atTop_iUnion_of_iUnion_eq_tsum hC m_add (partialSups f)
      (monotone_partialSups f) (hC.partialSups_mem hf) ?_
    rwa [← iSup_eq_iUnion, iSup_partialSups_eq]
  have h_tendsto' :
      Tendsto (fun n ↦ ∑ i in range (n + 1), m (f i)) atTop (𝓝 (∑' i, m (f i))) := by
    rw [tendsto_add_atTop_iff_nat (f := (fun k ↦ ∑ i in range k, m (f i))) 1]
    exact ENNReal.tendsto_nat_tsum _
  refine le_of_tendsto_of_tendsto' h_tendsto h_tendsto' fun n ↦ ?_
  rw [partialSups_eq_sUnion_image]
  refine (m.le_sum_of_subset_sUnion hC.isSetSemiring
    ((Finset.range (n + 1)).image f) ?_ ?_ subset_rfl).trans ?_
  · intro s
    rw [mem_coe, Finset.mem_image]
    rintro ⟨i, _, rfl⟩
    exact hf i
  · rw [← partialSups_eq_sUnion_image]
    exact hC.partialSups_mem hf n
  · exact Finset.sum_image_le _ _ _ fun _ _ ↦ zero_le _

end IsSetRing

end AddContent

end MeasureTheory
