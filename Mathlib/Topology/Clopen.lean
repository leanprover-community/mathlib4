/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.ContinuousOn
import Mathlib.Data.Set.BoolIndicator

/-!
# Clopen sets

A clopen set is a set that is both closed and open.
-/

open Set Filter Topology TopologicalSpace Classical

universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Clopen

protected lemma IsClopen.isOpen (hs : IsClopen s) : IsOpen s := hs.2
#align is_clopen.is_open IsClopen.isOpen

protected lemma IsClopen.isClosed (hs : IsClopen s) : IsClosed s := hs.1
#align is_clopen.is_closed IsClopen.isClosed

lemma isClopen_iff_frontier_eq_empty : IsClopen s ↔ frontier s = ∅ := by
  rw [IsClopen, ← closure_eq_iff_isClosed, ← interior_eq_iff_isOpen, frontier, diff_eq_empty]
  refine' ⟨fun h => (h.1.trans h.2.symm).subset, fun h => _⟩
  exact ⟨(h.trans interior_subset).antisymm subset_closure,
    interior_subset.antisymm (subset_closure.trans h)⟩
#align is_clopen_iff_frontier_eq_empty isClopen_iff_frontier_eq_empty

@[simp] alias ⟨IsClopen.frontier_eq, _⟩ := isClopen_iff_frontier_eq_empty
#align is_clopen.frontier_eq IsClopen.frontier_eq

lemma IsClopen.union (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∪ t) :=
  ⟨hs.1.union ht.1, hs.2.union ht.2⟩
#align is_clopen.union IsClopen.union

lemma IsClopen.inter (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩
#align is_clopen.inter IsClopen.inter

lemma isClopen_empty : IsClopen (∅ : Set X) := ⟨isClosed_empty, isOpen_empty⟩
#align is_clopen_empty isClopen_empty

lemma isClopen_univ : IsClopen (univ : Set X) := ⟨isClosed_univ, isOpen_univ⟩
#align is_clopen_univ isClopen_univ

lemma IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ :=
  ⟨hs.2.isClosed_compl, hs.1.isOpen_compl⟩
#align is_clopen.compl IsClopen.compl

@[simp]
lemma isClopen_compl_iff : IsClopen sᶜ ↔ IsClopen s :=
  ⟨fun h => compl_compl s ▸ IsClopen.compl h, IsClopen.compl⟩
#align is_clopen_compl_iff isClopen_compl_iff

lemma IsClopen.diff (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s \ t) :=
  hs.inter ht.compl
#align is_clopen.diff IsClopen.diff

lemma IsClopen.prod {t : Set Y} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ×ˢ t) :=
  ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩
#align is_clopen.prod IsClopen.prod

lemma isClopen_iUnion_of_finite [Finite Y] {s : Y → Set X} (h : ∀ i, IsClopen (s i)) :
    IsClopen (⋃ i, s i) :=
  ⟨isClosed_iUnion_of_finite (forall_and.1 h).1, isOpen_iUnion (forall_and.1 h).2⟩
#align is_clopen_Union isClopen_iUnion_of_finite

lemma Set.Finite.isClopen_biUnion {s : Set Y} {f : Y → Set X} (hs : s.Finite)
    (h : ∀ i ∈ s, IsClopen <| f i) : IsClopen (⋃ i ∈ s, f i) :=
  ⟨hs.isClosed_biUnion fun i hi => (h i hi).1, isOpen_biUnion fun i hi => (h i hi).2⟩
#align is_clopen_bUnion Set.Finite.isClopen_biUnion

lemma isClopen_biUnion_finset {s : Finset Y} {f : Y → Set X}
    (h : ∀ i ∈ s, IsClopen <| f i) : IsClopen (⋃ i ∈ s, f i) :=
 s.finite_toSet.isClopen_biUnion h
#align is_clopen_bUnion_finset isClopen_biUnion_finset

lemma isClopen_iInter_of_finite [Finite Y] {s : Y → Set X} (h : ∀ i, IsClopen (s i)) :
    IsClopen (⋂ i, s i) :=
  ⟨isClosed_iInter (forall_and.1 h).1, isOpen_iInter_of_finite (forall_and.1 h).2⟩
#align is_clopen_Inter isClopen_iInter_of_finite

lemma Set.Finite.isClopen_biInter {s : Set Y} (hs : s.Finite) {f : Y → Set X}
    (h : ∀ i ∈ s, IsClopen (f i)) : IsClopen (⋂ i ∈ s, f i) :=
  ⟨isClosed_biInter fun i hi => (h i hi).1, hs.isOpen_biInter fun i hi => (h i hi).2⟩
#align is_clopen_bInter Set.Finite.isClopen_biInter

lemma isClopen_biInter_finset {s : Finset Y} {f : Y → Set X}
    (h : ∀ i ∈ s, IsClopen (f i)) : IsClopen (⋂ i ∈ s, f i) :=
  s.finite_toSet.isClopen_biInter h
#align is_clopen_bInter_finset isClopen_biInter_finset

lemma IsClopen.preimage {s : Set Y} (h : IsClopen s) {f : X → Y} (hf : Continuous f) :
    IsClopen (f ⁻¹' s) :=
  ⟨h.1.preimage hf, h.2.preimage hf⟩
#align is_clopen.preimage IsClopen.preimage

lemma ContinuousOn.preimage_isClopen_of_isClopen {f : X → Y} {s : Set X} {t : Set Y}
    (hf : ContinuousOn f s) (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∩ f ⁻¹' t) :=
  ⟨ContinuousOn.preimage_isClosed_of_isClosed hf hs.1 ht.1,
    ContinuousOn.isOpen_inter_preimage hf hs.2 ht.2⟩
#align continuous_on.preimage_clopen_of_clopen ContinuousOn.preimage_isClopen_of_isClopen

/-- The intersection of a disjoint covering by two open sets of a clopen set will be clopen. -/
theorem isClopen_inter_of_disjoint_cover_clopen {s a b : Set X} (h : IsClopen s) (cover : s ⊆ a ∪ b)
    (ha : IsOpen a) (hb : IsOpen b) (hab : Disjoint a b) : IsClopen (s ∩ a) := by
  refine' ⟨_, IsOpen.inter h.2 ha⟩
  have : IsClosed (s ∩ bᶜ) := IsClosed.inter h.1 (isClosed_compl_iff.2 hb)
  convert this using 1
  refine' (inter_subset_inter_right s hab.subset_compl_right).antisymm _
  rintro x ⟨hx₁, hx₂⟩
  exact ⟨hx₁, by simpa [not_mem_of_mem_compl hx₂] using cover hx₁⟩
#align is_clopen_inter_of_disjoint_cover_clopen isClopen_inter_of_disjoint_cover_clopen

@[simp]
lemma isClopen_discrete [DiscreteTopology X] (s : Set X) : IsClopen s :=
  ⟨isClosed_discrete _, isOpen_discrete _⟩
#align is_clopen_discrete isClopen_discrete

-- Porting note (#10756): new lemma
lemma isClopen_range_inl : IsClopen (range (Sum.inl : X → X ⊕ Y)) :=
  ⟨isClosed_range_inl, isOpen_range_inl⟩

-- Porting note (#10756): new lemma
lemma isClopen_range_inr : IsClopen (range (Sum.inr : Y → X ⊕ Y)) :=
  ⟨isClosed_range_inr, isOpen_range_inr⟩

lemma isClopen_range_sigmaMk {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {i : ι} :
    IsClopen (Set.range (@Sigma.mk ι X i)) :=
  ⟨closedEmbedding_sigmaMk.isClosed_range, openEmbedding_sigmaMk.isOpen_range⟩
#align clopen_range_sigma_mk isClopen_range_sigmaMk

protected lemma QuotientMap.isClopen_preimage {f : X → Y} (hf : QuotientMap f) {s : Set Y} :
    IsClopen (f ⁻¹' s) ↔ IsClopen s :=
  and_congr hf.isClosed_preimage hf.isOpen_preimage
#align quotient_map.is_clopen_preimage QuotientMap.isClopen_preimage

lemma continuous_boolIndicator_iff_isClopen (U : Set X) :
    Continuous U.boolIndicator ↔ IsClopen U := by
  rw [continuous_bool_rng true, preimage_boolIndicator_true]
#align continuous_bool_indicator_iff_clopen continuous_boolIndicator_iff_isClopen

lemma continuousOn_boolIndicator_iff_isClopen (s U : Set X) :
    ContinuousOn U.boolIndicator s ↔ IsClopen (((↑) : s → X) ⁻¹' U) := by
  rw [continuousOn_iff_continuous_restrict, ← continuous_boolIndicator_iff_isClopen]
  rfl
#align continuous_on_indicator_iff_clopen continuousOn_boolIndicator_iff_isClopen

end Clopen
