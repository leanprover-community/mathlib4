/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Set.Image
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Compactness.NhdsKer

/-!
# Alexandrov-discrete topological spaces

This file defines Alexandrov-discrete spaces, aka finitely generated spaces.

A space is Alexandrov-discrete if the (arbitrary) intersection of open sets is open. As such,
the intersection of all neighborhoods of a set is a neighborhood itself. Hence every set has a
minimal neighborhood, which we call the *neighborhoods kernel* of the set.

## Main declarations

* `AlexandrovDiscrete`: Prop-valued typeclass for a topological space to be Alexandrov-discrete

## Tags

Alexandroff, discrete, finitely generated, fg space
-/

@[expose] public section

open Filter Set TopologicalSpace Topology

/-- A topological space is **Alexandrov-discrete** or **finitely generated** if the intersection of
a family of open sets is open. -/
@[mk_iff]
class AlexandrovDiscrete (α : Type*) [TopologicalSpace α] : Prop where
  /-- The intersection of a family of open sets is an open set. Use `isOpen_sInter` in the root
  namespace instead. -/
  protected isOpen_sInter : ∀ S : Set (Set α), (∀ s ∈ S, IsOpen s) → IsOpen (⋂₀ S)

variable {ι : Sort*} {κ : ι → Sort*} {α β : Type*}
section
variable [TopologicalSpace α] [TopologicalSpace β]

lemma alexandrovDiscrete_iff_isClosed :
    AlexandrovDiscrete α ↔ ∀ S : Set (Set α), (∀ s ∈ S, IsClosed s) → IsClosed (⋃₀ S) := by
  conv_lhs => tactic =>
    simp_rw +singlePass [alexandrovDiscrete_iff, compl_surjective.image_surjective.forall,
      forall_mem_image, ← compl_sUnion, isOpen_compl_iff]

instance IndiscreteTopology.toAlexandrovDiscrete [IndiscreteTopology α] : AlexandrovDiscrete α where
  isOpen_sInter := by grind [isOpen_iff]

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

lemma isClosed_sUnion (hS : ∀ s ∈ S, IsClosed s) : IsClosed (⋃₀ S) :=
  alexandrovDiscrete_iff_isClosed.mp inferInstance S hS

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

lemma Topology.IsInducing.alexandrovDiscrete [AlexandrovDiscrete α] {f : β → α} (h : IsInducing f) :
    AlexandrovDiscrete β where
  isOpen_sInter S hS := by
    simp_rw [h.isOpen_iff] at hS ⊢
    choose U hU htU using hS
    refine ⟨_, isOpen_iInter₂ hU, ?_⟩
    simp_rw [preimage_iInter, htU, sInter_eq_biInter]

end

set_option backward.isDefEq.respectTransparency false in
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

@[simp] lemma isOpen_nhdsKer : IsOpen (nhdsKer s) := by
  rw [nhdsKer_def]; exact isOpen_sInter fun _ ↦ And.left

lemma nhdsKer_mem_nhdsSet : nhdsKer s ∈ 𝓝ˢ s := isOpen_nhdsKer.mem_nhdsSet.2 subset_nhdsKer

@[simp] lemma nhdsKer_eq_iff_isOpen : nhdsKer s = s ↔ IsOpen s :=
  ⟨fun h ↦ h ▸ isOpen_nhdsKer, IsOpen.nhdsKer_eq⟩

@[simp] lemma nhdsKer_subset_iff_isOpen : nhdsKer s ⊆ s ↔ IsOpen s := by
  simp only [nhdsKer_eq_iff_isOpen.symm, Subset.antisymm_iff, subset_nhdsKer, and_true]

lemma nhdsKer_subset_iff : nhdsKer s ⊆ t ↔ ∃ U, IsOpen U ∧ s ⊆ U ∧ U ⊆ t :=
  ⟨fun h ↦ ⟨nhdsKer s, isOpen_nhdsKer, subset_nhdsKer, h⟩,
    fun ⟨_U, hU, hsU, hUt⟩ ↦ (nhdsKer_minimal hsU hU).trans hUt⟩

lemma nhdsKer_subset_iff_mem_nhdsSet : nhdsKer s ⊆ t ↔ t ∈ 𝓝ˢ s :=
  nhdsKer_subset_iff.trans mem_nhdsSet_iff_exists.symm

lemma nhdsKer_singleton_subset_iff_mem_nhds : nhdsKer {a} ⊆ t ↔ t ∈ 𝓝 a := by
  simp [nhdsKer_subset_iff_mem_nhdsSet]

lemma gc_nhdsKer_interior : GaloisConnection (nhdsKer : Set α → Set α) interior :=
  fun s t ↦ by simp [nhdsKer_subset_iff, subset_interior_iff]

@[simp] lemma principal_nhdsKer (s : Set α) : 𝓟 (nhdsKer s) = 𝓝ˢ s := by
  rw [← nhdsSet_nhdsKer, isOpen_nhdsKer.nhdsSet_eq]

lemma principal_nhdsKer_singleton (a : α) : 𝓟 (nhdsKer {a}) = 𝓝 a := by
  rw [principal_nhdsKer, nhdsSet_singleton]

lemma nhdsSet_basis_nhdsKer (s : Set α) :
    (𝓝ˢ s).HasBasis (fun _ : Unit => True) (fun _ => nhdsKer s) :=
  principal_nhdsKer s ▸ hasBasis_principal (nhdsKer s)

lemma nhds_basis_nhdsKer_singleton (a : α) :
    (𝓝 a).HasBasis (fun _ : Unit => True) (fun _ => nhdsKer {a}) :=
  principal_nhdsKer_singleton a ▸ hasBasis_principal (nhdsKer {a})

lemma isOpen_iff_forall_specializes : IsOpen s ↔ ∀ x y, x ⤳ y → y ∈ s → x ∈ s := by
  simp only [← nhdsKer_subset_iff_isOpen, Set.subset_def, mem_nhdsKer_iff_specializes, exists_imp,
    and_imp, @forall_comm (_ ⤳ _)]

omit [AlexandrovDiscrete α] in
lemma alexandrovDiscrete_iff_nhds : AlexandrovDiscrete α ↔ (∀ a : α, 𝓝 a = 𝓟 (nhdsKer {a})) where
  mp _ a := principal_nhdsKer_singleton a |>.symm
  mpr hα := by
    simp only [alexandrovDiscrete_iff_isClosed, isClosed_iff_clusterPt, ClusterPt, funext hα,
      inf_principal, principal_neBot_iff]
    intro S hS a ha
    rw [sUnion_eq_biUnion, inter_iUnion₂, nonempty_biUnion] at ha
    obtain ⟨s, hs, has⟩ := ha
    specialize hS s hs a has
    exact mem_sUnion_of_mem hS hs

lemma alexandrovDiscrete_coinduced {β : Type*} {f : α → β} :
    @AlexandrovDiscrete β (coinduced f ‹_›) :=
  @AlexandrovDiscrete.mk β (coinduced f ‹_›) fun S hS ↦ by
    rw [isOpen_coinduced, preimage_sInter]; exact isOpen_iInter₂ hS

instance AlexandrovDiscrete.toFirstCountable : FirstCountableTopology α where
  nhds_generated_countable a := ⟨{nhdsKer {a}}, countable_singleton _, by simp⟩

instance AlexandrovDiscrete.toLocallyCompactSpace : LocallyCompactSpace α where
  local_compact_nhds a _U hU := ⟨nhdsKer {a},
    isOpen_nhdsKer.mem_nhds <| subset_nhdsKer <| mem_singleton _,
      nhdsKer_singleton_subset_iff_mem_nhds.2 hU, isCompact_singleton.nhdsKer⟩

instance Subtype.instAlexandrovDiscrete {p : α → Prop} : AlexandrovDiscrete {a // p a} :=
  IsInducing.subtypeVal.alexandrovDiscrete

instance Quotient.instAlexandrovDiscrete {s : Setoid α} : AlexandrovDiscrete (Quotient s) :=
  alexandrovDiscrete_coinduced

instance Sum.instAlexandrovDiscrete : AlexandrovDiscrete (α ⊕ β) :=
  alexandrovDiscrete_coinduced.sup alexandrovDiscrete_coinduced

instance Sigma.instAlexandrovDiscrete {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, AlexandrovDiscrete (X i)] : AlexandrovDiscrete (Σ i, X i) :=
  alexandrovDiscrete_iSup fun _ ↦ alexandrovDiscrete_coinduced

instance Prod.instAlexandrovDiscrete : AlexandrovDiscrete (α × β) := by
  simp_rw [alexandrovDiscrete_iff_nhds, Prod.forall, nhds_prod_eq, ← principal_nhdsKer_singleton,
    prod_principal_principal, nhdsKer_pair, forall_true_iff]

instance Pi.instAlexandrovDiscreteOfFinite {ι : Type*} [Finite ι] {X : ι → Type*}
    [Π i, TopologicalSpace (X i)] [∀ i, AlexandrovDiscrete (X i)] :
    AlexandrovDiscrete (Π i, X i) := by
  simp_rw [alexandrovDiscrete_iff_nhds, nhds_pi, ← principal_nhdsKer_singleton,
    pi_principal, nhdsKer_singleton_pi, forall_true_iff]

end
