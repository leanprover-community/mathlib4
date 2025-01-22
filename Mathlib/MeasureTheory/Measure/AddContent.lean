/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.OuterMeasure.Induced
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

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

@[simp]
lemma accumulate_zero_nat {α : Type*}
  (s : ℕ → Set α) : Set.Accumulate s 0 = s 0 := by simp [Set.accumulate_def]

open Function in
theorem Set.disjoint_accumulate {α : Type*} {s : ℕ → Set α}
    (hs : Pairwise (Disjoint on s)) {i j : ℕ}
    (hij : i < j) : Disjoint (Set.Accumulate s i) (s j) := by
  rw [Set.accumulate_def]
  induction i with
  | zero => simp only [Nat.zero_eq, nonpos_iff_eq_zero, iUnion_iUnion_eq_left]; exact hs hij.ne
  | succ i hi =>
    rw [Set.biUnion_le_succ s i]
    exact Disjoint.union_left (hi ((Nat.lt_succ_self i).trans hij)) (hs hij.ne)

open scoped ENNReal in
open Filter Topology in
theorem ENNReal.tendsto_atTop_zero_const_sub_iff (f : ℕ → ℝ≥0∞) (a : ℝ≥0∞) (ha : a ≠ ∞)
    (hfa : ∀ n, f n ≤ a) :
    Tendsto (fun n ↦ a - f n) atTop (𝓝 0) ↔ Tendsto (fun n ↦ f n) atTop (𝓝 a) := by
  rw [ENNReal.tendsto_atTop_zero, ENNReal.tendsto_atTop ha]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩ <;> obtain ⟨N, hN⟩ := h ε hε
  · refine ⟨N, fun n hn ↦ ⟨?_, (hfa n).trans (le_add_right le_rfl)⟩⟩
    specialize hN n hn
    rw [tsub_le_iff_right] at hN ⊢
    rwa [add_comm]
  · refine ⟨N, fun n hn ↦ ?_⟩
    have hN_left := (hN n hn).1
    rw [tsub_le_iff_right] at hN_left ⊢
    rwa [add_comm]

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
  coe m s := m.toFun s
  coe_injective' m m' _ := by
    cases m
    cases m'
    congr

variable {m m' : AddContent C}

@[ext] protected lemma AddContent.ext (h : ∀ s, m s = m' s) : m = m' :=
  DFunLike.ext _ _ h

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
      mem_singleton_iff, Ne, id, forall_eq, true_and]
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

lemma addContent_diff_of_ne_top (m : AddContent C) (hC : IsSetRing C)
    (hm_ne_top : ∀ s ∈ C, m s ≠ ∞)
    {s t : Set α} (hs : s ∈ C) (ht : t ∈ C) (hts : t ⊆ s) :
    m (s \ t) = m s - m t := by
  have h_union : m (t ∪ s \ t) = m t + m (s \ t) :=
    addContent_union hC ht (hC.diff_mem hs ht) disjoint_sdiff_self_right
  simp_rw [Set.union_diff_self, Set.union_eq_right.mpr hts] at h_union
  rw [h_union, ENNReal.add_sub_cancel_left (hm_ne_top _ ht)]

lemma addContent_accumulate (m : AddContent C) (hC : IsSetRing C)
    {s : ℕ → Set α} (hs_disj : Pairwise (Function.onFun Disjoint s)) (hsC : ∀ i, s i ∈ C) (n : ℕ) :
      m (Set.Accumulate s n) = ∑ i in Finset.range (n + 1), m (s i) := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [Finset.sum_range_succ, ← hn, Set.accumulate_succ, addContent_union hC _ (hsC _)]
    · exact Set.disjoint_accumulate hs_disj (Nat.lt_succ_self n)
    · exact hC.accumulate_mem hsC n

end IsSetRing

open scoped ENNReal

open scoped Topology
open Filter

variable {α : Type*} {C : Set (Set α)}

/-- In a ring of sets, continuity of an additive content at `∅` implies σ-additivity.
This is not true in general in semirings, or without the hypothesis that `m` is finite. See the
examples 7 and 8 in Halmos' book Measure Theory (1974), page 40. -/
theorem addContent_iUnion_eq_sum_of_tendsto_zero (hC : IsSetRing C) (m : AddContent C)
    (hm_ne_top : ∀ s ∈ C, m s ≠ ∞)
    (hm_tendsto : ∀ ⦃s : ℕ → Set α⦄ (_ : ∀ n, s n ∈ C),
      Antitone s → (⋂ n, s n) = ∅ → Tendsto (fun n ↦ m (s n)) atTop (𝓝 0))
    ⦃f : ℕ → Set α⦄ (hf : ∀ i, f i ∈ C) (hUf : (⋃ i, f i) ∈ C)
    (h_disj : Pairwise (Function.onFun Disjoint f)) :
    m (⋃ i, f i) = ∑' i, m (f i) := by
  -- We use the continuity of `m` at `∅` on the sequence `n ↦ (⋃ i, f i) \ (set.accumulate f n)`
  let s : ℕ → Set α := fun n ↦ (⋃ i, f i) \ Set.Accumulate f n
  have hCs n : s n ∈ C := hC.diff_mem hUf (hC.accumulate_mem hf n)
  have h_tendsto : Tendsto (fun n ↦ m (s n)) atTop (𝓝 0) := by
    refine hm_tendsto hCs ?_ ?_
    · intro i j hij x hxj
      rw [Set.mem_diff] at hxj ⊢
      exact ⟨hxj.1, fun hxi ↦ hxj.2 (Set.monotone_accumulate hij hxi)⟩
    · simp_rw [s, Set.diff_eq]
      rw [Set.iInter_inter_distrib, Set.iInter_const, ← Set.compl_iUnion, Set.iUnion_accumulate]
      exact Set.inter_compl_self _
  have hmsn n : m (s n) = m (⋃ i, f i) - ∑ i in Finset.range (n + 1), m (f i) := by
    rw [addContent_diff_of_ne_top m hC hm_ne_top hUf (hC.accumulate_mem hf n)
      (Set.accumulate_subset_iUnion _), addContent_accumulate m hC h_disj hf n]
  simp_rw [hmsn] at h_tendsto
  refine tendsto_nhds_unique ?_ (ENNReal.tendsto_nat_tsum fun i ↦ m (f i))
  refine (Filter.tendsto_add_atTop_iff_nat 1).mp ?_
  rwa [ENNReal.tendsto_atTop_zero_const_sub_iff _ _ (hm_ne_top _ hUf) (fun n ↦ ?_)] at h_tendsto
  rw [← addContent_accumulate m hC h_disj hf]
  exact addContent_mono hC.isSetSemiring (hC.accumulate_mem hf n) hUf
    (Set.accumulate_subset_iUnion _)

theorem sUnion_eq_sum_of_union_eq_add (hC_empty : ∅ ∈ C)
    (hC_union : ∀ {s t : Set α}, s ∈ C → t ∈ C → s ∪ t ∈ C)
    (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0)
    (m_add : ∀ {s t : Set α} (_ : s ∈ C) (_ : t ∈ C), Disjoint s t → m (s ∪ t) = m s + m t)
    (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : Set.PairwiseDisjoint (I : Set (Set α)) id)
    (h_mem : ⋃₀ ↑I ∈ C) :
    m (⋃₀ I) = ∑ u in I, m u := by
  classical
  induction I using Finset.induction with
  | empty => simp only [Finset.coe_empty, Set.sUnion_empty, Finset.sum_empty, m_empty]
  | @insert s I hsI h =>
    rw [Finset.coe_insert] at *
    rw [Set.insert_subset_iff] at h_ss
    rw [Set.pairwiseDisjoint_insert_of_not_mem] at h_dis
    swap; · exact hsI
    have h_sUnion_mem : ⋃₀ ↑I ∈ C := by
      have (J : Finset (Set α)) : ↑J ⊆ C → ⋃₀ ↑J ∈ C := by
        induction J using Finset.induction with
        | empty => simp [hC_empty]
        | @insert s I _ h =>
          intro h_insert
          simp only [Finset.coe_insert, Set.sUnion_insert, Set.insert_subset_iff] at h_insert ⊢
          exact hC_union h_insert.1 (h h_insert.2)
      exact this I h_ss.2
    rw [Set.sUnion_insert, m_add h_ss.1 h_sUnion_mem (Set.disjoint_sUnion_right.mpr h_dis.2),
      Finset.sum_insert hsI, h h_ss.2 h_dis.1]
    rwa [Set.sUnion_insert] at h_mem

theorem sUnion_eq_sum_of_union_eq_add' (hC_empty : ∅ ∈ C)
    (hC_union : ∀ {s t : Set α}, s ∈ C → t ∈ C → s ∪ t ∈ C)
    {m : ∀ s : Set α, s ∈ C → ℝ≥0∞} (m_empty : m ∅ hC_empty = 0)
    (m_add : ∀ {s t : Set α} (hs : s ∈ C) (ht : t ∈ C),
      Disjoint s t → m (s ∪ t) (hC_union hs ht) = m s hs + m t ht)
    (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : Set.PairwiseDisjoint (I : Set (Set α)) id)
    (h_mem : ⋃₀ ↑I ∈ C) :
    m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.property) := by
  have h : extend m (⋃₀ ↑I) = ∑ u ∈ I, extend m u :=
    sUnion_eq_sum_of_union_eq_add hC_empty (fun hs ht ↦ hC_union hs ht) (extend m)
      (extend_empty hC_empty m_empty) ?_ I h_ss h_dis h_mem
  · rw [extend_eq m h_mem] at h
    refine h.trans ?_
    simp_rw [← extend_eq m, Finset.univ_eq_attach]
    exact (Finset.sum_attach _ _).symm
  · simp_rw [← extend_eq m] at m_add
    exact m_add

lemma IsSetRing.sUnion_eq_sum_of_union_eq_add (hC : IsSetRing C)
    {m : ∀ s : Set α, s ∈ C → ℝ≥0∞} (m_empty : m ∅ hC.empty_mem = 0)
    (m_add : ∀ {s t : Set α} (hs : s ∈ C) (ht : t ∈ C),
      Disjoint s t → m (s ∪ t) (hC.union_mem hs ht) = m s hs + m t ht)
    (I : Finset (Set α)) (h_ss : ↑I ⊆ C) (h_dis : Set.PairwiseDisjoint (I : Set (Set α)) id)
    (h_mem : ⋃₀ ↑I ∈ C) :
    m (⋃₀ I) h_mem = ∑ u : I, m u (h_ss u.property) :=
  sUnion_eq_sum_of_union_eq_add' hC.empty_mem (fun hs ht ↦ hC.union_mem hs ht) m_empty m_add I
    h_ss h_dis h_mem

end MeasureTheory
