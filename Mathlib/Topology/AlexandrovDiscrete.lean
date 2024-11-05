/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Image
import Mathlib.Topology.Bases
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Compactness.Exterior

/-!
# Alexandrov-discrete topological spaces

This file defines Alexandrov-discrete spaces, aka finitely generated spaces.

A space is Alexandrov-discrete if the (arbitrary) intersection of open sets is open. As such,
the intersection of all neighborhoods of a set is a neighborhood itself. Hence every set has a
minimal neighborhood, which we call the *exterior* of the set.

## Main declarations

* `AlexandrovDiscrete`: Prop-valued typeclass for a topological space to be Alexandrov-discrete

## Notes

The "minimal neighborhood of a set" construction is not named in the literature. We chose the name
"exterior" with analogy to the interior. `interior` and `exterior` have the same properties up to


## TODO

Finite product of Alexandrov-discrete spaces is Alexandrov-discrete.

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
  protected isOpen_sInter : ∀ S : Set (Set α), (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S)

variable {ι : Sort*} {κ : ι → Sort*} {α β : Type*}
section
variable [TopologicalSpace α] [TopologicalSpace β]

instance DiscreteTopology.toAlexandrovDiscrete [DiscreteTopology α] : AlexandrovDiscrete α where
  isOpen_sInter _ _ := isOpen_discrete _

instance Finite.toAlexandrovDiscrete [Finite α] : AlexandrovDiscrete α where
  isOpen_sInter S := (toFinite S).isOpen_sInter

section AlexandrovDiscrete
variable [AlexandrovDiscrete α] {S : Set (Set α)} {f : ι → Set α}

lemma isOpen_sInter : (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S) := AlexandrovDiscrete.isOpen_sInter _

lemma isOpen_iInter (hf : ∀ i, IsOpen (f i)) : IsOpen (⋂ i, f i) :=
  isOpen_sInter <| forall_mem_range.2 hf

lemma isOpen_iInter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsOpen (f i j)) :
    IsOpen (⋂ i, ⋂ j, f i j) :=
  isOpen_iInter fun _ ↦ isOpen_iInter <| hf _

lemma isClosed_sUnion (hS : ∀ s ∈ S, IsClosed s) : IsClosed (⋃₀ S) := by
  simp only [← isOpen_compl_iff, compl_sUnion] at hS ⊢; exact isOpen_sInter <| forall_mem_image.2 hS

lemma isClosed_iUnion (hf : ∀ i, IsClosed (f i)) : IsClosed (⋃ i, f i) :=
  isClosed_sUnion <| forall_mem_range.2 hf

lemma isClosed_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsClosed (f i j)) :
    IsClosed (⋃ i, ⋃ j, f i j) :=
  isClosed_iUnion fun _ ↦ isClosed_iUnion <| hf _

lemma isClopen_sInter (hS : ∀ s ∈ S, IsClopen s) : IsClopen (⋂₀ S) :=
  ⟨isClosed_sInter fun s hs ↦ (hS s hs).1, isOpen_sInter fun s hs ↦ (hS s hs).2⟩

lemma isClopen_iInter (hf : ∀ i, IsClopen (f i)) : IsClopen (⋂ i, f i) :=
  ⟨isClosed_iInter fun i ↦ (hf i).1, isOpen_iInter fun i ↦ (hf i).2⟩

lemma isClopen_iInter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsClopen (f i j)) :
    IsClopen (⋂ i, ⋂ j, f i j) :=
  isClopen_iInter fun _ ↦ isClopen_iInter <| hf _

lemma isClopen_sUnion (hS : ∀ s ∈ S, IsClopen s) : IsClopen (⋃₀ S) :=
  ⟨isClosed_sUnion fun s hs ↦ (hS s hs).1, isOpen_sUnion fun s hs ↦ (hS s hs).2⟩

lemma isClopen_iUnion (hf : ∀ i, IsClopen (f i)) : IsClopen (⋃ i, f i) :=
  ⟨isClosed_iUnion fun i ↦ (hf i).1, isOpen_iUnion fun i ↦ (hf i).2⟩

lemma isClopen_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsClopen (f i j)) :
    IsClopen (⋃ i, ⋃ j, f i j) :=
  isClopen_iUnion fun _ ↦ isClopen_iUnion <| hf _

lemma interior_iInter (f : ι → Set α) : interior (⋂ i, f i) = ⋂ i, interior (f i) :=
  (interior_maximal (iInter_mono fun _ ↦ interior_subset) <| isOpen_iInter fun _ ↦
    isOpen_interior).antisymm' <| subset_iInter fun _ ↦ interior_mono <| iInter_subset _ _

lemma interior_sInter (S : Set (Set α)) : interior (⋂₀ S) = ⋂ s ∈ S, interior s := by
  simp_rw [sInter_eq_biInter, interior_iInter]

lemma closure_iUnion (f : ι → Set α) : closure (⋃ i, f i) = ⋃ i, closure (f i) :=
  compl_injective <| by
    simpa only [← interior_compl, compl_iUnion] using interior_iInter fun i ↦ (f i)ᶜ

lemma closure_sUnion (S : Set (Set α)) : closure (⋃₀ S) = ⋃ s ∈ S, closure s := by
  simp_rw [sUnion_eq_biUnion, closure_iUnion]

end AlexandrovDiscrete

lemma IsInducing.alexandrovDiscrete [AlexandrovDiscrete α] {f : β → α} (h : IsInducing f) :
    AlexandrovDiscrete β where
  isOpen_sInter S hS := by
    simp_rw [h.isOpen_iff] at hS ⊢
    choose U hU htU using hS
    refine ⟨_, isOpen_iInter₂ hU, ?_⟩
    simp_rw [preimage_iInter, htU, sInter_eq_biInter]

@[deprecated (since := "2024-10-28")]
alias Inducing.alexandrovDiscrete := IsInducing.alexandrovDiscrete

end

lemma AlexandrovDiscrete.sup {t₁ t₂ : TopologicalSpace α} (_ : @AlexandrovDiscrete α t₁)
    (_ : @AlexandrovDiscrete α t₂) :
    @AlexandrovDiscrete α (t₁ ⊔ t₂) :=
  @AlexandrovDiscrete.mk α (t₁ ⊔ t₂) fun _S hS ↦
    ⟨@isOpen_sInter _ t₁ _ _ fun _s hs ↦ (hS _ hs).1, isOpen_sInter fun _s hs ↦ (hS _ hs).2⟩

lemma alexandrovDiscrete_iSup {t : ι → TopologicalSpace α} (_ : ∀ i, @AlexandrovDiscrete α (t i)) :
    @AlexandrovDiscrete α (⨆ i, t i) :=
  @AlexandrovDiscrete.mk α (⨆ i, t i)
    fun _S hS ↦ isOpen_iSup_iff.2
      fun i ↦ @isOpen_sInter _ (t i) _ _
        fun _s hs ↦ isOpen_iSup_iff.1 (hS _ hs) _

section
variable [TopologicalSpace α] [TopologicalSpace β] [AlexandrovDiscrete α] [AlexandrovDiscrete β]
  {s t : Set α} {a : α}

@[simp] lemma isOpen_exterior : IsOpen (exterior s) := by
  rw [exterior_def]; exact isOpen_sInter fun _ ↦ And.left

lemma exterior_mem_nhdsSet : exterior s ∈ 𝓝ˢ s := isOpen_exterior.mem_nhdsSet.2 subset_exterior

@[simp] lemma exterior_eq_iff_isOpen : exterior s = s ↔ IsOpen s :=
  ⟨fun h ↦ h ▸ isOpen_exterior, IsOpen.exterior_eq⟩

@[simp] lemma exterior_subset_iff_isOpen : exterior s ⊆ s ↔ IsOpen s := by
  simp only [exterior_eq_iff_isOpen.symm, Subset.antisymm_iff, subset_exterior, and_true]

lemma exterior_subset_iff : exterior s ⊆ t ↔ ∃ U, IsOpen U ∧ s ⊆ U ∧ U ⊆ t :=
  ⟨fun h ↦ ⟨exterior s, isOpen_exterior, subset_exterior, h⟩,
    fun ⟨_U, hU, hsU, hUt⟩ ↦ (exterior_minimal hsU hU).trans hUt⟩

lemma exterior_subset_iff_mem_nhdsSet : exterior s ⊆ t ↔ t ∈ 𝓝ˢ s :=
  exterior_subset_iff.trans mem_nhdsSet_iff_exists.symm

lemma exterior_singleton_subset_iff_mem_nhds : exterior {a} ⊆ t ↔ t ∈ 𝓝 a := by
  simp [exterior_subset_iff_mem_nhdsSet]

lemma gc_exterior_interior : GaloisConnection (exterior : Set α → Set α) interior :=
  fun s t ↦ by simp [exterior_subset_iff, subset_interior_iff]

@[simp] lemma principal_exterior (s : Set α) : 𝓟 (exterior s) = 𝓝ˢ s := by
  rw [← nhdsSet_exterior, isOpen_exterior.nhdsSet_eq]

lemma isOpen_iff_forall_specializes : IsOpen s ↔ ∀ x y, x ⤳ y → y ∈ s → x ∈ s := by
  simp only [← exterior_subset_iff_isOpen, Set.subset_def, mem_exterior_iff_specializes, exists_imp,
    and_imp, @forall_swap (_ ⤳ _)]

lemma alexandrovDiscrete_coinduced {β : Type*} {f : α → β} :
    @AlexandrovDiscrete β (coinduced f ‹_›) :=
  @AlexandrovDiscrete.mk β (coinduced f ‹_›) fun S hS ↦ by
    rw [isOpen_coinduced, preimage_sInter]; exact isOpen_iInter₂ hS

instance AlexandrovDiscrete.toFirstCountable : FirstCountableTopology α where
  nhds_generated_countable a := ⟨{exterior {a}}, countable_singleton _, by simp⟩

instance AlexandrovDiscrete.toLocallyCompactSpace : LocallyCompactSpace α where
  local_compact_nhds a _U hU := ⟨exterior {a},
    isOpen_exterior.mem_nhds <| subset_exterior <| mem_singleton _,
      exterior_singleton_subset_iff_mem_nhds.2 hU, isCompact_singleton.exterior⟩

instance Subtype.instAlexandrovDiscrete {p : α → Prop} : AlexandrovDiscrete {a // p a} :=
  IsInducing.subtypeVal.alexandrovDiscrete

instance Quotient.instAlexandrovDiscrete {s : Setoid α} : AlexandrovDiscrete (Quotient s) :=
  alexandrovDiscrete_coinduced

instance Sum.instAlexandrovDiscrete : AlexandrovDiscrete (α ⊕ β) :=
  alexandrovDiscrete_coinduced.sup alexandrovDiscrete_coinduced

instance Sigma.instAlexandrovDiscrete {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    [∀ i, AlexandrovDiscrete (π i)] : AlexandrovDiscrete (Σ i, π i) :=
  alexandrovDiscrete_iSup fun _ ↦ alexandrovDiscrete_coinduced

end
