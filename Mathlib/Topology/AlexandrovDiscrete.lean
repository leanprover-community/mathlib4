/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.Inseparable
import Mathlib.Topology.SubsetProperties

/-!
# Alexandrov-discrete topological spaces

This file defines Alexandrov-discrete spaces, aka finitely generated spaces.

A space is Alexandrov-discrete if the (arbitrary) intersection of open sets is open.

## TODO

Rest of the API

## Tags

Alexandroff, discrete, finitely generated, fg space
-/

open Filter Set TopologicalSpace
open scoped Topology

/-- A topological space is **Alexandrov-discrete** or **finitely generated** if the intersection of
a family of open sets is open. -/
class AlexandrovDiscrete (α : Type*) [TopologicalSpace α] : Prop where
  /-- The intersection of a family of open sets is an open set. Use `isOpen_sInter` in the root
  namespace instead. -/
  protected isOpen_sInter : ∀ s : Set (Set α), (∀ t ∈ s, IsOpen t) → IsOpen (⋂₀ s)

variable {ι : Sort*} {α : Type*} [TopologicalSpace α]

section AlexandrovDiscrete
variable [AlexandrovDiscrete α] {S : Set (Set α)} {f : ι → Set α}

lemma isOpen_sInter : (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S) := AlexandrovDiscrete.isOpen_sInter _

lemma isOpen_iInter (hf : ∀ i, IsOpen (f i)) : IsOpen (⋂ i, f i) :=
isOpen_sInter $ forall_range_iff.2 hf

lemma isClosed_sUnion (hS : ∀ s ∈ S, IsClosed s) : IsClosed (⋃₀ S) := by
  simp only [←isOpen_compl_iff, compl_sUnion] at hS ⊢; exact isOpen_sInter $ ball_image_iff.2 hS

lemma isClosed_iUnion (hf : ∀ i, IsClosed (f i)) : IsClosed (⋃ i, f i) :=
isClosed_sUnion $ forall_range_iff.2 hf

lemma isClopen_sUnion (hS : ∀ s ∈ S, IsClopen s) : IsClopen (⋃₀ S) :=
⟨isOpen_sUnion λ s hs ↦ (hS s hs).1, isClosed_sUnion λ s hs ↦ (hS s hs).2⟩

lemma isClopen_iUnion (hf : ∀ i, IsClopen (f i)) : IsClopen (⋃ i, f i) :=
⟨isOpen_iUnion λ i ↦ (hf i).1, isClosed_iUnion λ i ↦ (hf i).2⟩

lemma interior_iInter (f : ι → Set α) : interior (⋂ i, f i) = ⋂ i, interior (f i) :=
(interior_maximal (iInter_mono λ _ ↦ interior_subset) $ isOpen_iInter λ _ ↦
  isOpen_interior).antisymm' $ subset_iInter λ _ ↦ interior_mono $ iInter_subset _ _

lemma interior_sInter (S : Set (Set α)) : interior (⋂₀ S) = ⋂ s ∈ S, interior s := by
  simp_rw [sInter_eq_biInter, interior_iInter]

lemma closure_iUnion (f : ι → Set α) : closure (⋃ i, f i) = ⋃ i, closure (f i) :=
compl_injective $ by simpa only [←interior_compl, compl_iUnion] using interior_iInter λ i ↦ (f i)ᶜ

lemma closure_sUnion (S : Set (Set α)) : closure (⋃₀ S) = ⋃ s ∈ S, closure s := by
  simp_rw [sUnion_eq_biUnion, closure_iUnion]

end AlexandrovDiscrete

variable {s t : Set α} {x y : α}

/-- The *exterior* of a set is the intersection of all its neighborhoods. In an Alexandrov-discrete
space, this is the smallest neighborhood of the set. -/
def exterior (s : Set α) : Set α := (𝓝ˢ s).ker

lemma exterior_singleton_eq_ker_nhds (a : α) : exterior {a} = (𝓝 a).ker := by simp [exterior]

lemma exterior_def (s : Set α) : exterior s = ⋂₀ {t : Set α | IsOpen t ∧ s ⊆ t} := by
  ext a
  simp only [exterior, mem_ker, mem_sInter, mem_setOf_eq, and_imp, mem_nhdsSet_iff_forall]
  refine' ⟨λ hs t ht hts ↦ hs _ λ b hb ↦ ht.mem_nhds $ hts hb, λ hs t ht ↦ interior_subset $
    hs (interior t) isOpen_interior _⟩
  simpa only [←mem_interior_iff_mem_nhds] using ht

lemma subset_exterior_iff : s ⊆ exterior t ↔ ∀ U, IsOpen U → t ⊆ U → s ⊆ U := by
  simp [exterior_def]

lemma interior_subset_iff : interior s ⊆ t ↔ ∀ U, IsOpen U → U ⊆ s → U ⊆ t := by
  simp [interior]

lemma subset_exterior : s ⊆ exterior s := subset_exterior_iff.2 $ λ _ _ ↦ id

lemma exterior_minimal (h₁ : s ⊆ t) (h₂ : IsOpen t) : exterior s ⊆ t := by
  rw [exterior_def]; exact sInter_subset_of_mem ⟨h₂, h₁⟩

lemma IsOpen.exterior_eq (h : IsOpen s) : exterior s = s :=
(exterior_minimal Subset.rfl h).antisymm subset_exterior

lemma IsOpen.exterior_subset_iff (ht : IsOpen t) : exterior s ⊆ t ↔ s ⊆ t :=
⟨subset_exterior.trans, λ h ↦ exterior_minimal h ht⟩

@[mono] lemma exterior_mono : Monotone (exterior : Set α → Set α) :=
λ _s _t h ↦ ker_mono $ nhdsSet_mono h

@[simp] lemma exterior_empty : exterior (∅ : Set α) = ∅ := isOpen_empty.exterior_eq
@[simp] lemma exterior_univ : exterior (univ : Set α) = univ := isOpen_univ.exterior_eq

@[simp] lemma exterior_eq_empty : exterior s = ∅ ↔ s = ∅ :=
⟨eq_bot_mono subset_exterior, by rintro rfl; exact exterior_empty⟩

variable [AlexandrovDiscrete α]

@[simp] lemma isOpen_exterior : IsOpen (exterior s) := by
  rw [exterior_def]; exact isOpen_sInter $ λ _ ↦ And.left

@[simp] lemma exterior_eq_iff_isOpen : exterior s = s ↔ IsOpen s :=
  ⟨λ h ↦ h ▸ isOpen_exterior, IsOpen.exterior_eq⟩

@[simp] lemma exterior_subset_iff_isOpen : exterior s ⊆ s ↔ IsOpen s := by
  simp only [exterior_eq_iff_isOpen.symm, Subset.antisymm_iff, subset_exterior, and_true]

lemma exterior_subset : exterior s ⊆ t ↔ ∃ U, IsOpen U ∧ s ⊆ U ∧ U ⊆ t :=
⟨λ h ↦ ⟨exterior s, isOpen_exterior, subset_exterior, h⟩,
  λ ⟨_U, hU, hsU, hUt⟩ ↦ (exterior_minimal hsU hU).trans hUt⟩

lemma exterior_subset_iff_mem_nhds : exterior s ⊆ t ↔ t ∈ 𝓝ˢ s :=
exterior_subset.trans mem_nhdsSet_iff_exists.symm

lemma IsOpen.exterior_subset (ht : IsOpen t) : exterior s ⊆ t ↔ s ⊆ t :=
⟨subset_exterior.trans, λ h ↦ exterior_minimal h ht⟩

lemma gc_exterior_interior : GaloisConnection (exterior : Set α → Set α) interior :=
λ s t ↦ by simp [exterior_subset, subset_interior_iff]

@[simp] lemma exterior_exterior (s : Set α) : exterior (exterior s) = exterior s :=
isOpen_exterior.exterior_eq

@[simp] lemma exterior_union (s t : Set α) : exterior (s ∪ t) = exterior s ∪ exterior t :=
gc_exterior_interior.l_sup

@[simp] lemma nhdsSet_exterior (s : Set α) : 𝓝ˢ (exterior s) = 𝓟 (exterior s) :=
isOpen_exterior.nhdsSet_eq

@[simp] lemma exterior_subset_exterior : exterior s ⊆ exterior t ↔ 𝓝ˢ s ≤ 𝓝ˢ t := by
  refine ⟨?_, λ h ↦ ker_mono h⟩
  simp_rw [le_def, ←exterior_subset_iff_mem_nhds]
  exact λ h u ↦ h.trans

lemma specializes_iff_exterior_subset : x ⤳ y ↔ exterior {x} ⊆ exterior {y} := by
  simp [Specializes]

lemma isOpen_iff_forall_specializes : IsOpen s ↔ ∀ x y, x ⤳ y → y ∈ s → x ∈ s := by
  refine' ⟨λ hs x y hxy ↦ hxy.mem_open hs, λ hs ↦ _⟩
  simp_rw [specializes_iff_exterior_subset] at hs
  simp_rw [isOpen_iff_mem_nhds, mem_nhds_iff]
  rintro a ha
  refine ⟨_, λ b hb ↦ hs _ _ ?_ ha, isOpen_exterior, subset_exterior $ mem_singleton _⟩
  rwa [isOpen_exterior.exterior_subset, singleton_subset_iff]
