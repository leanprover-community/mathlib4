/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Topology.Maps.Basic

/-!
# Constructions of new topological spaces from old ones

This file constructs products, sums, subtypes and quotients of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, sum, disjoint union, subspace, quotient space

-/

noncomputable section

open Topology TopologicalSpace Set Filter Function

universe u v u' v'

variable {X : Type u} {Y : Type v} {Z W ε ζ : Type*}

instance instTopologicalSpaceSum [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X ⊕ Y) :=
  coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

open Sum

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]

theorem continuous_sum_dom {f : X ⊕ Y → Z} :
    Continuous f ↔ Continuous (f ∘ Sum.inl) ∧ Continuous (f ∘ Sum.inr) :=
  (continuous_sup_dom (t₁ := TopologicalSpace.coinduced Sum.inl _)
    (t₂ := TopologicalSpace.coinduced Sum.inr _)).trans <|
    continuous_coinduced_dom.and continuous_coinduced_dom

theorem continuous_sumElim {f : X → Z} {g : Y → Z} :
    Continuous (Sum.elim f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sum_dom

@[deprecated (since := "2025-02-20")] alias continuous_sum_elim := continuous_sumElim

@[continuity, fun_prop]
theorem Continuous.sumElim {f : X → Z} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.elim f g) :=
  continuous_sumElim.2 ⟨hf, hg⟩

@[deprecated (since := "2025-02-20")] alias Continuous.sum_elim := Continuous.sumElim

@[continuity, fun_prop]
theorem continuous_isLeft : Continuous (isLeft : X ⊕ Y → Bool) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]
theorem continuous_isRight : Continuous (isRight : X ⊕ Y → Bool) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]
theorem continuous_inl : Continuous (@inl X Y) := ⟨fun _ => And.left⟩

@[continuity, fun_prop]
theorem continuous_inr : Continuous (@inr X Y) := ⟨fun _ => And.right⟩

@[fun_prop, continuity]
lemma continuous_sum_swap : Continuous (@Sum.swap X Y) :=
  Continuous.sumElim continuous_inr continuous_inl

theorem isOpen_sum_iff {s : Set (X ⊕ Y)} : IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsOpen (inr ⁻¹' s) :=
  Iff.rfl

theorem isClosed_sum_iff {s : Set (X ⊕ Y)} :
    IsClosed s ↔ IsClosed (inl ⁻¹' s) ∧ IsClosed (inr ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_sum_iff, preimage_compl]

theorem isOpenMap_inl : IsOpenMap (@inl X Y) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inl_injective]

theorem isOpenMap_inr : IsOpenMap (@inr X Y) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inr_injective]

theorem isClosedMap_inl : IsClosedMap (@inl X Y) := fun u hu ↦ by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inl_injective]

theorem isClosedMap_inr : IsClosedMap (@inr X Y) := fun u hu ↦ by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inr_injective]

protected lemma Topology.IsOpenEmbedding.inl : IsOpenEmbedding (@inl X Y) :=
  .of_continuous_injective_isOpenMap continuous_inl inl_injective isOpenMap_inl

@[deprecated (since := "2024-10-30")] alias isOpenEmbedding_inl := IsOpenEmbedding.inl

@[deprecated (since := "2024-10-18")]
alias openEmbedding_inl := IsOpenEmbedding.inl

protected lemma Topology.IsOpenEmbedding.inr : IsOpenEmbedding (@inr X Y) :=
  .of_continuous_injective_isOpenMap continuous_inr inr_injective isOpenMap_inr

@[deprecated (since := "2024-10-30")] alias isOpenEmbedding_inr := IsOpenEmbedding.inr

@[deprecated (since := "2024-10-18")]
alias openEmbedding_inr := IsOpenEmbedding.inr

protected lemma Topology.IsEmbedding.inl : IsEmbedding (@inl X Y) := IsOpenEmbedding.inl.1
protected lemma Topology.IsEmbedding.inr : IsEmbedding (@inr X Y) := IsOpenEmbedding.inr.1

@[deprecated (since := "2024-10-26")]
alias embedding_inr := IsEmbedding.inr

lemma isOpen_range_inl : IsOpen (range (inl : X → X ⊕ Y)) := IsOpenEmbedding.inl.2
lemma isOpen_range_inr : IsOpen (range (inr : Y → X ⊕ Y)) := IsOpenEmbedding.inr.2

theorem isClosed_range_inl : IsClosed (range (inl : X → X ⊕ Y)) := by
  rw [← isOpen_compl_iff, compl_range_inl]
  exact isOpen_range_inr

theorem isClosed_range_inr : IsClosed (range (inr : Y → X ⊕ Y)) := by
  rw [← isOpen_compl_iff, compl_range_inr]
  exact isOpen_range_inl

theorem Topology.IsClosedEmbedding.inl : IsClosedEmbedding (inl : X → X ⊕ Y) :=
  ⟨.inl, isClosed_range_inl⟩

@[deprecated (since := "2024-10-30")] alias isClosedEmbedding_inl := IsClosedEmbedding.inl

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_inl := IsClosedEmbedding.inl

theorem Topology.IsClosedEmbedding.inr : IsClosedEmbedding (inr : Y → X ⊕ Y) :=
  ⟨.inr, isClosed_range_inr⟩

@[deprecated (since := "2024-10-30")] alias isClosedEmbedding_inr := IsClosedEmbedding.inr

@[deprecated (since := "2024-10-20")]
alias closedEmbedding_inr := IsClosedEmbedding.inr

theorem nhds_inl (x : X) : 𝓝 (inl x : X ⊕ Y) = map inl (𝓝 x) :=
  (IsOpenEmbedding.inl.map_nhds_eq _).symm

theorem nhds_inr (y : Y) : 𝓝 (inr y : X ⊕ Y) = map inr (𝓝 y) :=
  (IsOpenEmbedding.inr.map_nhds_eq _).symm

@[simp]
theorem continuous_sumMap {f : X → Y} {g : Z → W} :
    Continuous (Sum.map f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sumElim.trans <|
    IsEmbedding.inl.continuous_iff.symm.and IsEmbedding.inr.continuous_iff.symm

@[deprecated (since := "2025-02-21")] alias continuous_sum_map := continuous_sumMap

@[continuity, fun_prop]
theorem Continuous.sumMap {f : X → Y} {g : Z → W} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.map f g) :=
  continuous_sumMap.2 ⟨hf, hg⟩

@[deprecated (since := "2025-02-21")] alias Continuous.sum_map := Continuous.sumMap

theorem isOpenMap_sum {f : X ⊕ Y → Z} :
    IsOpenMap f ↔ (IsOpenMap fun a => f (inl a)) ∧ IsOpenMap fun b => f (inr b) := by
  simp only [isOpenMap_iff_nhds_le, Sum.forall, nhds_inl, nhds_inr, Filter.map_map, comp_def]

theorem IsOpenMap.sumMap {f : X → Y} {g : Z → W} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.map f g) :=
  isOpenMap_sum.2 ⟨isOpenMap_inl.comp hf, isOpenMap_inr.comp hg⟩

@[simp]
theorem isOpenMap_sumElim {f : X → Z} {g : Y → Z} :
    IsOpenMap (Sum.elim f g) ↔ IsOpenMap f ∧ IsOpenMap g := by
  simp only [isOpenMap_sum, elim_inl, elim_inr]

@[deprecated (since := "2025-02-20")] alias isOpenMap_sum_elim := isOpenMap_sumElim

theorem IsOpenMap.sumElim {f : X → Z} {g : Y → Z} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.elim f g) :=
  isOpenMap_sumElim.2 ⟨hf, hg⟩

@[deprecated (since := "2025-02-20")] alias IsOpenMap.sum_elim := IsOpenMap.sumElim

lemma IsOpenEmbedding.sumElim {f : X → Z} {g : Y → Z}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (h : Injective (Sum.elim f g)) :
    IsOpenEmbedding (Sum.elim f g) := by
  rw [isOpenEmbedding_iff_continuous_injective_isOpenMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩

theorem isClosedMap_sum {f : X ⊕ Y → Z} :
    IsClosedMap f ↔ (IsClosedMap fun a => f (.inl a)) ∧ IsClosedMap fun b => f (.inr b) := by
  constructor
  · intro h
    exact ⟨h.comp IsClosedEmbedding.inl.isClosedMap, h.comp IsClosedEmbedding.inr.isClosedMap⟩
  · rintro h Z hZ
    rw [isClosed_sum_iff] at hZ
    convert (h.1 _ hZ.1).union (h.2 _ hZ.2)
    ext
    simp only [mem_image, Sum.exists, mem_union, mem_preimage]

theorem IsClosedMap.sumMap {f : X → Y} {g : Z → W} (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (Sum.map f g) :=
  isClosedMap_sum.2 ⟨isClosedMap_inl.comp hf, isClosedMap_inr.comp hg⟩

@[simp]
theorem isClosedMap_sumElim {f : X → Z} {g : Y → Z} :
    IsClosedMap (Sum.elim f g) ↔ IsClosedMap f ∧ IsClosedMap g := by
  simp only [isClosedMap_sum, Sum.elim_inl, Sum.elim_inr]

theorem IsClosedMap.sumElim {f : X → Z} {g : Y → Z} (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (Sum.elim f g) :=
  isClosedMap_sumElim.2 ⟨hf, hg⟩

lemma IsClosedEmbedding.sumElim {f : X → Z} {g : Y → Z}
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) (h : Injective (Sum.elim f g)) :
    IsClosedEmbedding (Sum.elim f g) := by
  rw [IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩
