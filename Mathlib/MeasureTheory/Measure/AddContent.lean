/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.MeasureTheory.OuterMeasure.Induced

-- somewhere else
lemma Finset.sum_image_le_of_nonneg {ι α β : Type*} [DecidableEq α]
    [OrderedAddCommMonoid β] [SMulPosMono ℕ β]
    {J : Finset ι} {g : ι → α} {f : α → β} (hf : ∀ u ∈ J.image g, 0 ≤ f u) :
    ∑ u in J.image g, f u ≤ ∑ u in J, f (g u) := by
  rw [sum_comp f g]
  refine sum_le_sum fun a hag ↦ ?_
  obtain ⟨i, hi, hig⟩ := Finset.mem_image.mp hag
  conv_lhs => rw [← one_nsmul (f a)]
  refine smul_le_smul_of_nonneg_right ?_ (hf a hag)
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, card_pos]
  exact ⟨i, mem_filter.mpr ⟨hi, hig⟩⟩


-- part of PR #15294
@[to_additive]
lemma Finset.prod_image_of_disjoint {ι α β : Type*} [PartialOrder α] [OrderBot α] [DecidableEq α]
    [CommMonoid β] {g : α → β}
    (hg_bot : g ⊥ = 1) {f : ι → α} {I : Finset ι} (hf_disj : (I : Set ι).PairwiseDisjoint f) :
    ∏ s in I.image f, g s = ∏ i in I, g (f i) := by

  rw [prod_image']
  intro n hnI
  by_cases hfn : f n = ⊥
  · simp only [hfn, hg_bot]
    refine (prod_eq_one fun i hi ↦ ?_).symm
    rw [mem_filter] at hi
    rw [hi.2, hg_bot]
  · classical
    suffices filter (fun j ↦ f j = f n) I = filter (fun j ↦ j = n) I by
      simp only [this, prod_filter, prod_ite_eq', if_pos hnI]
    refine filter_congr (fun j hj ↦ ?_)
    refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
    by_contra hij
    have h_dis : Disjoint (f j) (f n) := hf_disj hj hnI hij
    rw [h] at h_dis
    exact hfn (disjoint_self.mp h_dis)


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

/-- For an additive content `m` on a semiring and `s t : Set α` with `s ⊆ t`, we can write
`m t = m s + ∑ i in hC.diffFinset ht hs, m i`.-/
theorem addContent_eq_add_diffFinset_of_subset (hC : IsSetSemiring C) (m : Set α → ℝ≥0∞)
    (m_add : ∀ (I : Finset (Set α)) (_ : ↑I ⊆ C) (_ : PairwiseDisjoint (I : Set (Set α)) id)
        (_h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)
    (hs : s ∈ C) (ht : t ∈ C) (hst : s ⊆ t) [DecidableEq (Set α)] :
    m t = m s + ∑ i in hC.diffFinset ht hs, m i := by
  classical
  conv_lhs => rw [← hC.sUnion_insert_diffFinset ht hs hst]
  rw [← coe_insert, m_add]
  · rw [sum_insert]
    exact hC.not_mem_diffFinset ht hs
  · rw [coe_insert]
    exact Set.insert_subset hs (hC.diffFinset_subset ht hs)
  · rw [coe_insert]
    exact hC.pairwiseDisjoint_insert_diffFinset ht hs
  · rw [coe_insert]
    rwa [hC.sUnion_insert_diffFinset ht hs hst]

/-- For an additive content `m` on a semiring, `s : Set α` and `I : Set (Set α)` pairwise
disjoint with `⋃₀ I ⊆ s`, we can write `m s = ∑ i ∈ I, m i + ∑ i ∈ hC.diffFinset₀ hs hI, m i`.-/
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

variable (hC : IsSetSemiring C) (m : Set α → ℝ≥0∞)
  (m_add : ∀ (I : Finset (Set α)) (_h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
    (_h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) = ∑ u in I, m u)

lemma addContent_sUnion_le_sum {m : AddContent C} (hC : IsSetSemiring C)
    (J : Finset (Set α)) (h_ss : ↑J ⊆ C) (h_mem : ⋃₀ ↑J ∈ C) :
    m (⋃₀ ↑J) ≤ ∑ u in J, m u := by
  classical
  rw [hC.allDiffFinset₀'_sUnion h_ss, addContent_sUnion (hC.allDiffFinset₀'_subset_semiring h_ss)
    (hC.allDiffFinset₀'_pairwiseDisjoint h_ss)]
  · rw [sum_disjiUnion]
    apply sum_le_sum
    intro x hx
    exact sum_addContent_le_of_subset hC (hC.allDiffFinset₀'_subsets_semiring h_ss hx)
      (hC.allDiffFinset₀'_pairwiseDisjoints h_ss hx) (h_ss hx) (hC.allDiffFinset₀'_subsets h_ss hx)
  · exact hC.allDiffFinset₀'_sUnion h_ss ▸ h_mem

lemma addContent_le_sum_of_subset_sUnion {m : AddContent C} (hC : IsSetSemiring C)
    (J : Finset (Set α)) (h_ss : ↑J ⊆ C) (ht : t ∈ C) (htJ : t ⊆ ⋃₀ ↑J) :
    m t ≤ ∑ u in J, m u := by
  -- we can't apply `addContent_mono` and `addContent_sUnion_le_sum` because `⋃₀ ↑J` might not
  -- be in `C`
  classical
  let Jt := J.image (fun u ↦ t ∩ u)
  have ht_eq : t = ⋃₀ Jt := by
    rw [coe_image, sUnion_image, ← inter_iUnion₂, inter_eq_self_of_subset_left]
    rwa [← sUnion_eq_biUnion]
  rw [ht_eq]
  refine (addContent_sUnion_le_sum hC Jt ?_ ?_).trans ?_
  · intro s
    simp only [Jt, coe_image, Set.mem_image, mem_coe, forall_exists_index, and_imp]
    rintro u hu rfl
    exact hC.inter_mem _ ht _ (h_ss hu)
  · rwa [← ht_eq]
  · refine (Finset.sum_image_le_of_nonneg fun _ _ ↦ zero_le _).trans (sum_le_sum fun u hu ↦ ?_)
    exact addContent_mono hC (hC.inter_mem _ ht _ (h_ss hu)) (h_ss hu) inter_subset_right

/-- If an `AddContent` is σ-subadditive on a semi-ring of sets, then it is σ-additive. -/
theorem addContent_iUnion_eq_tsum_of_disjoint_of_addContent_iUnion_le {m : AddContent C}
    (hC : IsSetSemiring C)
    (m_subadd : ∀ (f : ℕ → Set α) (_ : ∀ i, f i ∈ C) (_ : ⋃ i, f i ∈ C)
      (_hf_disj : Pairwise (Function.onFun Disjoint f)), m (⋃ i, f i) ≤ ∑' i, m (f i))
    (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (hf_Union : (⋃ i, f i) ∈ C)
    (hf_disj : Pairwise (Function.onFun Disjoint f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  refine le_antisymm (m_subadd f hf hf_Union hf_disj) ?_
  refine tsum_le_of_sum_le ENNReal.summable fun I ↦ ?_
  classical
  rw [← Finset.sum_image_of_disjoint addContent_empty (hf_disj.pairwiseDisjoint _)]
  refine sum_addContent_le_of_subset hC (I := I.image f) ?_ ?_ hf_Union ?_
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
  · simp only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact fun i _ ↦ subset_iUnion _ i


end IsSetSemiring

section ExtendContent

variable {m : ∀ s : Set α, s ∈ C → ℝ≥0∞}

/-- Build an `AddContent` from an additive function defined on a semiring of sets. -/
noncomputable def extendContent (hC : IsSetSemiring C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop)) :
    AddContent C where
  toFun := extend m
  empty' := extend_empty hC.empty_mem m_empty
  sUnion' I h_ss h_dis h_mem := by
    simp_rw [← extend_eq m] at m_add
    rw [m_add I h_ss h_dis h_mem, univ_eq_attach, sum_attach]

theorem extendContent_eq_extend (hC : IsSetSemiring C) (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop)) :
    extendContent hC m m_empty m_add = extend m := rfl

theorem extendContent_eq (hC : IsSetSemiring C) (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (hs : s ∈ C) :
    extendContent hC m m_empty m_add s = m s hs := by
  rw [extendContent_eq_extend, extend_eq]

theorem extendContent_eq_top (hC : IsSetSemiring C) (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (_h_dis : PairwiseDisjoint (I : Set (Set α)) id)
      (h_mem : ⋃₀ ↑I ∈ C), m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.prop))
    (hs : s ∉ C) :
    extendContent hC m m_empty m_add s = ∞ := by
  rw [extendContent_eq_extend, extend_eq_top m hs]

end ExtendContent

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
