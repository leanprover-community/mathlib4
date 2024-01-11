/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Order.Filter.Pi
import Mathlib.Topology.Bases
import Mathlib.Data.Finset.Order
import Mathlib.Data.Set.Accumulate
import Mathlib.Data.Set.BoolIndicator
import Mathlib.Topology.Bornology.Basic
import Mathlib.Topology.LocallyFinite
import Mathlib.Order.Minimal

/-!
# Clopen sets

A clopen set is a set that is both open and closed.
-/

open Set Filter Topology TopologicalSpace Classical

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {π : ι → Type*}

variable [TopologicalSpace α] [TopologicalSpace β] {s t : Set α}

section Clopen

-- porting note: todo: redefine as `IsClosed s ∧ IsOpen s`
/-- A set is clopen if it is both open and closed. -/
def IsClopen (s : Set α) : Prop :=
  IsOpen s ∧ IsClosed s
#align is_clopen IsClopen

protected theorem IsClopen.isOpen (hs : IsClopen s) : IsOpen s := hs.1
#align is_clopen.is_open IsClopen.isOpen

protected theorem IsClopen.isClosed (hs : IsClopen s) : IsClosed s := hs.2
#align is_clopen.is_closed IsClopen.isClosed

theorem isClopen_iff_frontier_eq_empty {s : Set α} : IsClopen s ↔ frontier s = ∅ := by
  rw [IsClopen, ← closure_eq_iff_isClosed, ← interior_eq_iff_isOpen, frontier, diff_eq_empty]
  refine' ⟨fun h => (h.2.trans h.1.symm).subset, fun h => _⟩
  exact ⟨interior_subset.antisymm (subset_closure.trans h),
    (h.trans interior_subset).antisymm subset_closure⟩
#align is_clopen_iff_frontier_eq_empty isClopen_iff_frontier_eq_empty

alias ⟨IsClopen.frontier_eq, _⟩ := isClopen_iff_frontier_eq_empty
#align is_clopen.frontier_eq IsClopen.frontier_eq

theorem IsClopen.union {s t : Set α} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∪ t) :=
  ⟨hs.1.union ht.1, hs.2.union ht.2⟩
#align is_clopen.union IsClopen.union

theorem IsClopen.inter {s t : Set α} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩
#align is_clopen.inter IsClopen.inter

@[simp] theorem isClopen_empty : IsClopen (∅ : Set α) := ⟨isOpen_empty, isClosed_empty⟩
#align is_clopen_empty isClopen_empty

@[simp] theorem isClopen_univ : IsClopen (univ : Set α) := ⟨isOpen_univ, isClosed_univ⟩
#align is_clopen_univ isClopen_univ

theorem IsClopen.compl {s : Set α} (hs : IsClopen s) : IsClopen sᶜ :=
  ⟨hs.2.isOpen_compl, hs.1.isClosed_compl⟩
#align is_clopen.compl IsClopen.compl

@[simp]
theorem isClopen_compl_iff {s : Set α} : IsClopen sᶜ ↔ IsClopen s :=
  ⟨fun h => compl_compl s ▸ IsClopen.compl h, IsClopen.compl⟩
#align is_clopen_compl_iff isClopen_compl_iff

theorem IsClopen.diff {s t : Set α} (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s \ t) :=
  hs.inter ht.compl
#align is_clopen.diff IsClopen.diff

theorem IsClopen.prod {s : Set α} {t : Set β} (hs : IsClopen s) (ht : IsClopen t) :
    IsClopen (s ×ˢ t) :=
  ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩
#align is_clopen.prod IsClopen.prod

theorem isClopen_iUnion_of_finite {β : Type*} [Finite β] {s : β → Set α} (h : ∀ i, IsClopen (s i)) :
    IsClopen (⋃ i, s i) :=
  ⟨isOpen_iUnion (forall_and.1 h).1, isClosed_iUnion_of_finite (forall_and.1 h).2⟩
#align is_clopen_Union isClopen_iUnion_of_finite

theorem Set.Finite.isClopen_biUnion {β : Type*} {s : Set β} {f : β → Set α} (hs : s.Finite)
    (h : ∀ i ∈ s, IsClopen <| f i) : IsClopen (⋃ i ∈ s, f i) :=
  ⟨isOpen_biUnion fun i hi => (h i hi).1, hs.isClosed_biUnion fun i hi => (h i hi).2⟩
#align is_clopen_bUnion Set.Finite.isClopen_biUnion

theorem isClopen_biUnion_finset {β : Type*} {s : Finset β} {f : β → Set α}
    (h : ∀ i ∈ s, IsClopen <| f i) : IsClopen (⋃ i ∈ s, f i) :=
 s.finite_toSet.isClopen_biUnion  h
#align is_clopen_bUnion_finset isClopen_biUnion_finset

theorem isClopen_iInter_of_finite {β : Type*} [Finite β] {s : β → Set α} (h : ∀ i, IsClopen (s i)) :
    IsClopen (⋂ i, s i) :=
  ⟨isOpen_iInter_of_finite (forall_and.1 h).1, isClosed_iInter (forall_and.1 h).2⟩
#align is_clopen_Inter isClopen_iInter_of_finite

theorem Set.Finite.isClopen_biInter {β : Type*} {s : Set β} (hs : s.Finite) {f : β → Set α}
    (h : ∀ i ∈ s, IsClopen (f i)) : IsClopen (⋂ i ∈ s, f i) :=
  ⟨hs.isOpen_biInter fun i hi => (h i hi).1, isClosed_biInter fun i hi => (h i hi).2⟩
#align is_clopen_bInter Set.Finite.isClopen_biInter

theorem isClopen_biInter_finset {β : Type*} {s : Finset β} {f : β → Set α}
    (h : ∀ i ∈ s, IsClopen (f i)) : IsClopen (⋂ i ∈ s, f i) :=
  s.finite_toSet.isClopen_biInter h
#align is_clopen_bInter_finset isClopen_biInter_finset

theorem IsClopen.preimage {s : Set β} (h : IsClopen s) {f : α → β} (hf : Continuous f) :
    IsClopen (f ⁻¹' s) :=
  ⟨h.1.preimage hf, h.2.preimage hf⟩
#align is_clopen.preimage IsClopen.preimage

theorem ContinuousOn.preimage_clopen_of_clopen {f : α → β} {s : Set α} {t : Set β}
    (hf : ContinuousOn f s) (hs : IsClopen s) (ht : IsClopen t) : IsClopen (s ∩ f ⁻¹' t) :=
  ⟨ContinuousOn.preimage_open_of_open hf hs.1 ht.1,
    ContinuousOn.preimage_closed_of_closed hf hs.2 ht.2⟩
#align continuous_on.preimage_clopen_of_clopen ContinuousOn.preimage_clopen_of_clopen

/-- The intersection of a disjoint covering by two open sets of a clopen set will be clopen. -/
theorem isClopen_inter_of_disjoint_cover_clopen {Z a b : Set α} (h : IsClopen Z) (cover : Z ⊆ a ∪ b)
    (ha : IsOpen a) (hb : IsOpen b) (hab : Disjoint a b) : IsClopen (Z ∩ a) := by
  refine' ⟨IsOpen.inter h.1 ha, _⟩
  have : IsClosed (Z ∩ bᶜ) := IsClosed.inter h.2 (isClosed_compl_iff.2 hb)
  convert this using 1
  refine' (inter_subset_inter_right Z hab.subset_compl_right).antisymm _
  rintro x ⟨hx₁, hx₂⟩
  exact ⟨hx₁, by simpa [not_mem_of_mem_compl hx₂] using cover hx₁⟩
#align is_clopen_inter_of_disjoint_cover_clopen isClopen_inter_of_disjoint_cover_clopen

@[simp]
theorem isClopen_discrete [DiscreteTopology α] (x : Set α) : IsClopen x :=
  ⟨isOpen_discrete _, isClosed_discrete _⟩
#align is_clopen_discrete isClopen_discrete

-- porting note: new lemma
theorem isClopen_range_inl : IsClopen (range (Sum.inl : α → α ⊕ β)) :=
  ⟨isOpen_range_inl, isClosed_range_inl⟩

-- porting note: new lemma
theorem isClopen_range_inr : IsClopen (range (Sum.inr : β → α ⊕ β)) :=
  ⟨isOpen_range_inr, isClosed_range_inr⟩

theorem isClopen_range_sigmaMk {ι : Type*} {σ : ι → Type*} [∀ i, TopologicalSpace (σ i)] {i : ι} :
    IsClopen (Set.range (@Sigma.mk ι σ i)) :=
  ⟨openEmbedding_sigmaMk.open_range, closedEmbedding_sigmaMk.closed_range⟩
#align clopen_range_sigma_mk isClopen_range_sigmaMk

protected theorem QuotientMap.isClopen_preimage {f : α → β} (hf : QuotientMap f) {s : Set β} :
    IsClopen (f ⁻¹' s) ↔ IsClopen s :=
  and_congr hf.isOpen_preimage hf.isClosed_preimage
#align quotient_map.is_clopen_preimage QuotientMap.isClopen_preimage

variable {X : Type*} [TopologicalSpace X]

theorem continuous_boolIndicator_iff_clopen (U : Set X) :
    Continuous U.boolIndicator ↔ IsClopen U := by
  rw [continuous_to_bool, preimage_boolIndicator_true]
#align continuous_bool_indicator_iff_clopen continuous_boolIndicator_iff_clopen

theorem continuousOn_boolIndicator_iff_clopen (s U : Set X) :
    ContinuousOn U.boolIndicator s ↔ IsClopen (((↑) : s → X) ⁻¹' U) := by
  rw [continuousOn_iff_continuous_restrict, ← continuous_boolIndicator_iff_clopen]
  rfl
#align continuous_on_indicator_iff_clopen continuousOn_boolIndicator_iff_clopen

end Clopen
