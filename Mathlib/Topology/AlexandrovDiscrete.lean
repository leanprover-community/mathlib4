/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Image
import Mathlib.Topology.Bases
import Mathlib.Tactic.Peel
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Compactness.Compact

/-!
# Alexandrov-discrete topological spaces

This file defines Alexandrov-discrete spaces, aka finitely generated spaces.

A space is Alexandrov-discrete if the (arbitrary) intersection of open sets is open. As such,
the intersection of all neighborhoods of a set is a neighborhood itself. Hence every set has a
minimal neighborhood, which we call the *exterior* of the set.

## Main declarations

* `AlexandrovDiscrete`: Prop-valued typeclass for a topological space to be Alexandrov-discrete
* `exterior`: Intersection of all neighborhoods of a set. When the space is Alexandrov-discrete,
  this is the minimal neighborhood of the set.

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

variable {s t : Set α} {a x y : α}

/-- The *exterior* of a set is the intersection of all its neighborhoods. In an Alexandrov-discrete
space, this is the smallest neighborhood of the set.

Note that this construction is unnamed in the literature. We choose the name in analogy to
`interior`. -/
def exterior (s : Set α) : Set α := (𝓝ˢ s).ker

lemma exterior_singleton_eq_ker_nhds (a : α) : exterior {a} = (𝓝 a).ker := by simp [exterior]

@[simp]
theorem mem_exterior_singleton : x ∈ exterior {y} ↔ x ⤳ y := by
  rw [exterior_singleton_eq_ker_nhds, ker_nhds_eq_specializes, mem_setOf]

lemma exterior_def (s : Set α) : exterior s = ⋂₀ {t : Set α | IsOpen t ∧ s ⊆ t} :=
  (hasBasis_nhdsSet _).ker.trans sInter_eq_biInter.symm

lemma mem_exterior : a ∈ exterior s ↔ ∀ U, IsOpen U → s ⊆ U → a ∈ U := by simp [exterior_def]

lemma subset_exterior_iff : s ⊆ exterior t ↔ ∀ U, IsOpen U → t ⊆ U → s ⊆ U := by
  simp [exterior_def]

lemma subset_exterior : s ⊆ exterior s := subset_exterior_iff.2 fun _ _ ↦ id

lemma exterior_minimal (h₁ : s ⊆ t) (h₂ : IsOpen t) : exterior s ⊆ t := by
  rw [exterior_def]; exact sInter_subset_of_mem ⟨h₂, h₁⟩

lemma IsOpen.exterior_eq (h : IsOpen s) : exterior s = s :=
  (exterior_minimal Subset.rfl h).antisymm subset_exterior

lemma IsOpen.exterior_subset (ht : IsOpen t) : exterior s ⊆ t ↔ s ⊆ t :=
  ⟨subset_exterior.trans, fun h ↦ exterior_minimal h ht⟩

@[deprecated (since := "2024-09-18")] alias IsOpen.exterior_subset_iff := IsOpen.exterior_subset

@[simp]
theorem exterior_iUnion {ι : Sort*} (s : ι → Set α) :
    exterior (⋃ i, s i) = ⋃ i, exterior (s i) := by
  simp only [exterior, nhdsSet_iUnion, ker_iSup]

@[simp]
theorem exterior_union (s t : Set α) : exterior (s ∪ t) = exterior s ∪ exterior t := by
  simp only [exterior, nhdsSet_union, ker_sup]

@[simp]
theorem exterior_sUnion (S : Set (Set α)) : exterior (⋃₀ S) = ⋃ s ∈ S, exterior s := by
  simp only [sUnion_eq_biUnion, exterior_iUnion]

theorem mem_exterior_iff_specializes : a ∈ exterior s ↔ ∃ b ∈ s, a ⤳ b := calc
  a ∈ exterior s ↔ a ∈ exterior (⋃ x ∈ s, {x}) := by simp
  _ ↔ ∃ b ∈ s, a ⤳ b := by
    simp only [exterior_iUnion, mem_exterior_singleton, mem_iUnion₂, exists_prop]

@[mono] lemma exterior_mono : Monotone (exterior : Set α → Set α) :=
  fun _s _t h ↦ ker_mono <| nhdsSet_mono h

/-- This name was used to be used for the `Iff` version,
see `exterior_subset_exterior_iff_nhdsSet`.
-/
@[gcongr] lemma exterior_subset_exterior (h : s ⊆ t) : exterior s ⊆ exterior t := exterior_mono h

@[simp] lemma exterior_subset_exterior_iff_nhdsSet : exterior s ⊆ exterior t ↔ 𝓝ˢ s ≤ 𝓝ˢ t := by
  simp (config := {contextual := true}) only [subset_exterior_iff, (hasBasis_nhdsSet _).ge_iff,
    and_imp, IsOpen.mem_nhdsSet, IsOpen.exterior_subset]

theorem exterior_eq_exterior_iff_nhdsSet : exterior s = exterior t ↔ 𝓝ˢ s = 𝓝ˢ t := by
  simp [le_antisymm_iff]

lemma specializes_iff_exterior_subset : x ⤳ y ↔ exterior {x} ⊆ exterior {y} := by
  simp [Specializes]

@[simp] lemma exterior_empty : exterior (∅ : Set α) = ∅ := isOpen_empty.exterior_eq
@[simp] lemma exterior_univ : exterior (univ : Set α) = univ := isOpen_univ.exterior_eq

@[simp] lemma exterior_eq_empty : exterior s = ∅ ↔ s = ∅ :=
  ⟨eq_bot_mono subset_exterior, by rintro rfl; exact exterior_empty⟩

@[simp] lemma nhdsSet_exterior (s : Set α) : 𝓝ˢ (exterior s) = 𝓝ˢ s := by
  refine le_antisymm ((hasBasis_nhdsSet _).ge_iff.2 ?_) (nhdsSet_mono subset_exterior)
  exact fun U ⟨hUo, hsU⟩ ↦ hUo.mem_nhdsSet.2 <| hUo.exterior_subset.2 hsU

@[simp] lemma exterior_exterior (s : Set α) : exterior (exterior s) = exterior s := by
  simp only [exterior_eq_exterior_iff_nhdsSet, nhdsSet_exterior]

lemma Inducing.alexandrovDiscrete [AlexandrovDiscrete α] {f : β → α} (h : Inducing f) :
    AlexandrovDiscrete β where
  isOpen_sInter S hS := by
    simp_rw [h.isOpen_iff] at hS ⊢
    choose U hU htU using hS
    refine ⟨_, isOpen_iInter₂ hU, ?_⟩
    simp_rw [preimage_iInter, htU, sInter_eq_biInter]

theorem IsCompact.exterior_iff : IsCompact (exterior s) ↔ IsCompact s := by
  simp only [isCompact_iff_finite_subcover]
  peel with ι U hUo
  simp only [(isOpen_iUnion hUo).exterior_subset,
    (isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ hUo i).exterior_subset]

protected alias ⟨IsCompact.of_exterior, IsCompact.exterior⟩ := IsCompact.exterior_iff

@[deprecated IsCompact.exterior (since := "2024-09-18")]
lemma Set.Finite.isCompact_exterior (hs : s.Finite) : IsCompact (exterior s) :=
  hs.isCompact.exterior

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
  {s t : Set α} {a x y : α}

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
      exterior_singleton_subset_iff_mem_nhds.2 hU, (finite_singleton _).isCompact.exterior⟩

instance Subtype.instAlexandrovDiscrete {p : α → Prop} : AlexandrovDiscrete {a // p a} :=
  inducing_subtype_val.alexandrovDiscrete

instance Quotient.instAlexandrovDiscrete {s : Setoid α} : AlexandrovDiscrete (Quotient s) :=
  alexandrovDiscrete_coinduced

instance Sum.instAlexandrovDiscrete : AlexandrovDiscrete (α ⊕ β) :=
  alexandrovDiscrete_coinduced.sup alexandrovDiscrete_coinduced

instance Sigma.instAlexandrovDiscrete {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    [∀ i, AlexandrovDiscrete (π i)] : AlexandrovDiscrete (Σ i, π i) :=
  alexandrovDiscrete_iSup fun _ ↦ alexandrovDiscrete_coinduced

end
