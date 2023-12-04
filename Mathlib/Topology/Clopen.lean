/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.ContinuousOn
import Mathlib.Data.Set.BoolIndicator

/-!
# Clopen sets

A clopen set is a set that is both open and closed.
-/

open Set Filter Topology TopologicalSpace Classical

universe u v

variable {X : Type u} {Y : Type v} {ι : Type*}

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

section Clopen

-- porting note: todo: redefine as `IsClosed s ∧ IsOpen s`
/-- A set is clopen if it is both open and closed. -/
def IsClopen (s : Set X) : Prop :=
  IsOpen s ∧ IsClosed s
#align is_clopen IsClopen

protected theorem IsClopen.isOpen (hs : IsClopen s) : IsOpen s := hs.1
#align is_clopen.is_open IsClopen.isOpen

protected theorem IsClopen.isClosed (hs : IsClopen s) : IsClosed s := hs.2
#align is_clopen.is_closed IsClopen.isClosed

theorem isClopen_iff_frontier_eq_empty : IsClopen s ↔ frontier s = ∅ := by
  rw [IsClopen, ← closure_eq_iff_isClosed, ← interior_eq_iff_isOpen, frontier, diff_eq_empty]
  refine' ⟨fun h => (h.2.trans h.1.symm).subset, fun h => _⟩
  exact ⟨interior_subset.antisymm (subset_closure.trans h),
    (h.trans interior_subset).antisymm subset_closure⟩
#align is_clopen_iff_frontier_eq_empty isClopen_iff_frontier_eq_empty

alias ⟨IsClopen.frontier_eq, _⟩ := isClopen_iff_frontier_eq_empty
#align is_clopen.frontier_eq IsClopen.frontier_eq

theorem IsClopen.union (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∪ t) :=
  ⟨hs.1.union ht.1, hs.2.union ht.2⟩
#align is_clopen.union IsClopen.union

theorem IsClopen.inter (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩
#align is_clopen.inter IsClopen.inter

@[simp] theorem isClopen_empty : IsClopen (∅ : Set X) := ⟨isOpen_empty, isClosed_empty⟩
#align is_clopen_empty isClopen_empty

@[simp] theorem isClopen_univ : IsClopen (univ : Set X) := ⟨isOpen_univ, isClosed_univ⟩
#align is_clopen_univ isClopen_univ

theorem IsClopen.compl (hs : IsClopen s) : IsClopen sᶜ :=
  ⟨hs.2.isOpen_compl, hs.1.isClosed_compl⟩
#align is_clopen.compl IsClopen.compl

@[simp]
theorem isClopen_compl_iff : IsClopen sᶜ ↔ IsClopen s :=
  ⟨fun h => compl_compl s ▸ IsClopen.compl h, IsClopen.compl⟩
#align is_clopen_compl_iff isClopen_compl_iff

theorem IsClopen.diff (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s \ t) :=
  hs.inter ht.compl
#align is_clopen.diff IsClopen.diff

theorem IsClopen.prod {t : Set Y} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ×ˢ t) :=
  ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩
#align is_clopen.prod IsClopen.prod

theorem isClopen_iUnion_of_finite [Finite Y] {s : Y → Set X} (h : ∀ i, IsClopen (s i)) :
    IsClopen (⋃ i, s i) :=
  ⟨isOpen_iUnion (forall_and.1 h).1, isClosed_iUnion_of_finite (forall_and.1 h).2⟩
#align is_clopen_Union isClopen_iUnion_of_finite

theorem Set.Finite.isClopen_biUnion {s : Set Y} {f : Y → Set X} (hs : s.Finite)
    (h : ∀ i ∈ s, IsClopen <| f i) : IsClopen (⋃ i ∈ s, f i) :=
  ⟨isOpen_biUnion fun i hi => (h i hi).1, hs.isClosed_biUnion fun i hi => (h i hi).2⟩
#align is_clopen_bUnion Set.Finite.isClopen_biUnion

theorem isClopen_biUnion_finset {s : Finset Y} {f : Y → Set X}
    (h : ∀ i ∈ s, IsClopen <| f i) : IsClopen (⋃ i ∈ s, f i) :=
 s.finite_toSet.isClopen_biUnion h
#align is_clopen_bUnion_finset isClopen_biUnion_finset

theorem isClopen_iInter_of_finite [Finite Y] {s : Y → Set X} (h : ∀ i, IsClopen (s i)) :
    IsClopen (⋂ i, s i) :=
  ⟨isOpen_iInter_of_finite (forall_and.1 h).1, isClosed_iInter (forall_and.1 h).2⟩
#align is_clopen_Inter isClopen_iInter_of_finite

theorem Set.Finite.isClopen_biInter {s : Set Y} (hs : s.Finite) {f : Y → Set X}
    (h : ∀ i ∈ s, IsClopen (f i)) : IsClopen (⋂ i ∈ s, f i) :=
  ⟨hs.isOpen_biInter fun i hi => (h i hi).1, isClosed_biInter fun i hi => (h i hi).2⟩
#align is_clopen_bInter Set.Finite.isClopen_biInter

theorem isClopen_biInter_finset {s : Finset Y} {f : Y → Set X}
    (h : ∀ i ∈ s, IsClopen (f i)) : IsClopen (⋂ i ∈ s, f i) :=
  s.finite_toSet.isClopen_biInter h
#align is_clopen_bInter_finset isClopen_biInter_finset

theorem IsClopen.preimage {s : Set Y} (h : IsClopen s) {f : X → Y} (hf : Continuous f) :
    IsClopen (f ⁻¹' s) :=
  ⟨h.1.preimage hf, h.2.preimage hf⟩
#align is_clopen.preimage IsClopen.preimage

theorem ContinuousOn.preimage_isClopen_of_isClopen {f : X → Y} {s : Set X} {t : Set Y}
    (hf : ContinuousOn f s) (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∩ f ⁻¹' t) :=
  ⟨ContinuousOn.isOpen_inter_preimage hf hs.1 ht.1,
    ContinuousOn.preimage_isClosed_of_isClosed hf hs.2 ht.2⟩
#align continuous_on.preimage_clopen_of_clopen ContinuousOn.preimage_isClopen_of_isClopen

/-- The intersection of a disjoint covering by two open sets of a clopen set will be clopen. -/
theorem isClopen_inter_of_disjoint_cover_clopen {s a b : Set X} (h : IsClopen s) (cover : s ⊆ a ∪ b)
    (ha : IsOpen a) (hb : IsOpen b) (hab : Disjoint a b) : IsClopen (s ∩ a) := by
  refine' ⟨IsOpen.inter h.1 ha, _⟩
  have : IsClosed (s ∩ bᶜ) := IsClosed.inter h.2 (isClosed_compl_iff.2 hb)
  convert this using 1
  refine' (inter_subset_inter_right s hab.subset_compl_right).antisymm _
  rintro x ⟨hx₁, hx₂⟩
  exact ⟨hx₁, by simpa [not_mem_of_mem_compl hx₂] using cover hx₁⟩
#align is_clopen_inter_of_disjoint_cover_clopen isClopen_inter_of_disjoint_cover_clopen

@[simp]
theorem isClopen_discrete [DiscreteTopology X] (s : Set X) : IsClopen s :=
  ⟨isOpen_discrete _, isClosed_discrete _⟩
#align is_clopen_discrete isClopen_discrete

-- porting note: new lemma
theorem isClopen_range_inl : IsClopen (range (Sum.inl : X → X ⊕ Y)) :=
  ⟨isOpen_range_inl, isClosed_range_inl⟩

-- porting note: new lemma
theorem isClopen_range_inr : IsClopen (range (Sum.inr : Y → X ⊕ Y)) :=
  ⟨isOpen_range_inr, isClosed_range_inr⟩

theorem isClopen_range_sigmaMk {X : ι → Type*} [∀ i, TopologicalSpace (X i)] {i : ι} :
    IsClopen (Set.range (@Sigma.mk ι X i)) :=
  ⟨openEmbedding_sigmaMk.open_range, closedEmbedding_sigmaMk.closed_range⟩
#align clopen_range_sigma_mk isClopen_range_sigmaMk

protected theorem QuotientMap.isClopen_preimage {f : X → Y} (hf : QuotientMap f) {s : Set Y} :
    IsClopen (f ⁻¹' s) ↔ IsClopen s :=
  and_congr hf.isOpen_preimage hf.isClosed_preimage
#align quotient_map.is_clopen_preimage QuotientMap.isClopen_preimage

theorem continuous_boolIndicator_iff_isClopen (U : Set X) :
    Continuous U.boolIndicator ↔ IsClopen U := by
  constructor
  · intro hc
    rw [← U.preimage_boolIndicator_true]
    exact ⟨(isOpen_discrete _).preimage hc, (isClosed_discrete _).preimage hc⟩
  · refine' fun hU => ⟨fun s _ => _⟩
    rcases U.preimage_boolIndicator s with (h | h | h | h) <;> rw [h]
    exacts [isOpen_univ, hU.1, hU.2.isOpen_compl, isOpen_empty]
#align continuous_bool_indicator_iff_clopen continuous_boolIndicator_iff_isClopen

theorem continuousOn_boolIndicator_iff_isClopen (s U : Set X) :
    ContinuousOn U.boolIndicator s ↔ IsClopen (((↑) : s → X) ⁻¹' U) := by
  rw [continuousOn_iff_continuous_restrict, ← continuous_boolIndicator_iff_isClopen]
  rfl
#align continuous_on_indicator_iff_clopen continuousOn_boolIndicator_iff_isClopen

end Clopen
