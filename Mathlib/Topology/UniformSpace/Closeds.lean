/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Hausdorff uniformity

This file defines the Hausdorff uniformity on the types of closed subsets, compact subsets and
and nonempty compact subsets of a uniform space. This is the generalization of the uniformity
induced by the Hausdorff metric to hyperspaces of uniform spaces.
-/

@[expose] public section

open Topology
open scoped Uniformity

variable {α β : Type*}

section hausdorffEntourage

open SetRel

/-- The set of pairs of sets contained in each other's thickening with respect to an entourage. -/
def hausdorffEntourage (U : SetRel α α) : SetRel (Set α) (Set α) :=
  {x | x.1 ⊆ U.preimage x.2 ∧ x.2 ⊆ U.image x.1}

theorem mem_hausdorffEntourage (U : SetRel α α) (s t : Set α) :
    (s, t) ∈ hausdorffEntourage U ↔ s ⊆ U.preimage t ∧ t ⊆ U.image s :=
  Iff.rfl

@[gcongr]
theorem hausdorffEntourage_mono {U V : SetRel α α} (h : U ⊆ V) :
    hausdorffEntourage U ⊆ hausdorffEntourage V := by
  unfold hausdorffEntourage
  gcongr

theorem monotone_hausdorffEntourage : Monotone (hausdorffEntourage (α := α)) :=
  fun _ _ => hausdorffEntourage_mono

instance isRefl_hausdorffEntourage (U : SetRel α α) [U.IsRefl] :
    (hausdorffEntourage U).IsRefl :=
  ⟨fun _ => ⟨U.self_subset_preimage _, U.self_subset_image _⟩⟩

@[simp]
theorem inv_hausdorffEntourage (U : SetRel α α) :
    (hausdorffEntourage U).inv = hausdorffEntourage U.inv :=
  Set.ext fun _ => And.comm

instance isSymm_hausdorffEntourage (U : SetRel α α) [U.IsSymm] :
    (hausdorffEntourage U).IsSymm := by
  rw [← inv_eq_self_iff, inv_hausdorffEntourage, inv_eq_self]

theorem hausdorffEntourage_comp (U V : SetRel α α) :
    hausdorffEntourage (U ○ V) = hausdorffEntourage U ○ hausdorffEntourage V := by
  apply subset_antisymm
  · intro ⟨s, t⟩ ⟨hst, hts⟩
    simp only [mem_comp, mem_hausdorffEntourage] at *
    refine ⟨U.image s ∩ V.preimage t, ⟨?_, Set.inter_subset_left⟩, ⟨Set.inter_subset_right, ?_⟩⟩
    · intro x hx
      obtain ⟨z, hz, y, hxy, hyz⟩ := hst hx
      exact ⟨y, ⟨⟨x, hx, hxy⟩, ⟨z, hz, hyz⟩⟩, hxy⟩
    · intro z hz
      obtain ⟨x, hx, y, hxy, hyz⟩ := hts hz
      exact ⟨y, ⟨⟨x, hx, hxy⟩, ⟨z, hz, hyz⟩⟩, hyz⟩
  · intro ⟨s₁, s₃⟩ ⟨s₂, ⟨h₁₂, h₂₁⟩, ⟨h₂₃, h₃₂⟩⟩
    simp only at *
    grw [mem_hausdorffEntourage, preimage_comp, ← h₂₃, ← h₁₂, image_comp, ← h₂₁, ← h₃₂]
    exact ⟨subset_rfl, subset_rfl⟩

instance isTrans_hausdorffEntourage (U : SetRel α α) [U.IsTrans] :
    (hausdorffEntourage U).IsTrans := by
  grw [isTrans_iff_comp_subset_self, ← hausdorffEntourage_comp, comp_subset_self]

@[simp]
theorem singleton_mem_hausdorffEntourage (U : SetRel α α) (x y : α) :
    ({x}, {y}) ∈ hausdorffEntourage U ↔ (x, y) ∈ U := by
  simp [hausdorffEntourage]

end hausdorffEntourage

variable [UniformSpace α] [UniformSpace β]

variable (α) in
/-- The Hausdorff uniformity on the powerset of a uniform space. Used for defining the uniformities
on `Closeds`, `Compacts` and `NonemptyCompacts`.
See note [reducible non-instances]. -/
protected abbrev UniformSpace.hausdorff : UniformSpace (Set α) := .ofCore
  { uniformity := (𝓤 α).lift' hausdorffEntourage
    refl := by
      simp_rw [Filter.principal_le_lift', SetRel.id_subset_iff]
      intro (U : SetRel α α) hU
      have : U.IsRefl := ⟨fun _ => refl_mem_uniformity hU⟩
      exact isRefl_hausdorffEntourage U
    symm :=
      Filter.tendsto_lift'.mpr fun U hU => Filter.mem_of_superset
        (Filter.mem_lift' (symm_le_uniformity hU)) (inv_hausdorffEntourage U).symm.subset
    comp := by
      rw [Filter.le_lift']
      intro U hU
      obtain ⟨V, hV, hVU⟩ := comp_mem_uniformity_sets hU
      refine Filter.mem_of_superset (Filter.mem_lift' (Filter.mem_lift' hV)) ?_
      grw [← hausdorffEntourage_comp, hVU] }

attribute [local instance] UniformSpace.hausdorff

theorem Filter.HasBasis.uniformity_hausdorff
    {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (Set α)).HasBasis p (hausdorffEntourage ∘ s) :=
  h.lift' monotone_hausdorffEntourage

namespace UniformSpace.hausdorff

theorem isOpen_inter_nonempty_of_isOpen {U : Set α} (hU : IsOpen U) :
    IsOpen {s | (s ∩ U).Nonempty} := by
  rw [isOpen_iff_mem_nhds]
  intro s ⟨x, hx₁, hx₂⟩
  rw [← hU.mem_nhds_iff, mem_nhds_iff] at hx₂
  obtain ⟨V, hV, hVU⟩ := hx₂
  rw [mem_nhds_iff]
  refine ⟨_, Filter.mem_lift' hV, ?_⟩
  rintro s' ⟨hs', -⟩
  obtain ⟨y, hy, hxy⟩ := hs' hx₁
  exact ⟨y, hy, hVU hxy⟩

theorem isClosed_powerset {F : Set α} (hF : IsClosed F) :
    IsClosed F.powerset := by
  simp_rw [Set.powerset, ← isOpen_compl_iff, Set.compl_setOf, ← Set.inter_compl_nonempty_iff]
  exact isOpen_inter_nonempty_of_isOpen hF.isOpen_compl

theorem isClopen_singleton_empty : IsClopen {(∅ : Set α)} := by
  constructor
  · rw [← Set.powerset_empty]
    exact isClosed_powerset isClosed_empty
  · simp_rw [isOpen_iff_mem_nhds, Set.mem_singleton_iff, forall_eq, nhds_eq_uniformity]
    filter_upwards [Filter.mem_lift' <| Filter.mem_lift' Filter.univ_mem] with F ⟨_, hF⟩
    simpa using hF

theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α → Set α) where
  injective := Set.singleton_injective
  comap_uniformity := by
    change Filter.comap _ (Filter.lift' _ _) = _
    simp_rw [Filter.comap_lift'_eq, Function.comp_def, Set.preimage,
      singleton_mem_hausdorffEntourage]
    exact Filter.lift'_id

theorem isClosedEmbedding_singleton [T0Space α] :
    Topology.IsClosedEmbedding ({·} : α → Set α) where
  __ := isUniformEmbedding_singleton.isEmbedding
  isClosed_range := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro s hs
    rcases Set.eq_empty_or_nonempty s with rfl | h
    · rwa [(isOpen_singleton_iff_nhds_eq_pure _).mp isClopen_singleton_empty.isOpen,
        Filter.mem_pure]
    rcases h.exists_eq_singleton_or_nontrivial with ⟨x, rfl⟩ | ⟨x, hx, y, hy, hxy⟩
    · cases hs <| Set.mem_range_self x
    obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hxy
    filter_upwards [(isOpen_inter_nonempty_of_isOpen hU).inter (isOpen_inter_nonempty_of_isOpen hV)
      |>.mem_nhds ⟨⟨x, hx, hxU⟩, ⟨y, hy, hyV⟩⟩]
    rintro _ ⟨hzU, hzV⟩ ⟨z, rfl⟩
    rw [Set.mem_setOf, Set.singleton_inter_nonempty] at hzU hzV
    exact hUV.notMem_of_mem_left hzU hzV

end UniformSpace.hausdorff

/-- When `Set` is equipped with the Hausdorff uniformity, taking the image under a uniformly
continuous map is uniformly continuous. -/
theorem UniformContinuous.image_hausdorff {f : α → β} (hf : UniformContinuous f) :
    UniformContinuous (f '' ·) := by
  refine Filter.tendsto_lift'.mpr fun U hU => ?_
  filter_upwards [Filter.mem_lift' (hf hU)] with ⟨s, t⟩ ⟨h₁, h₂⟩
  simp_rw [mem_hausdorffEntourage, Set.image_subset_iff]
  exact ⟨h₁.trans fun x ⟨y, hy, hxy⟩ => ⟨f y, Set.mem_image_of_mem f hy, hxy⟩,
    h₂.trans fun x ⟨y, hy, hxy⟩ => ⟨f y, Set.mem_image_of_mem f hy, hxy⟩⟩

/-- When `Set` is equipped with the Hausdorff uniformity, taking the image under a uniform
inducing map is uniform inducing. -/
theorem IsUniformInducing.image_hausdorff {f : α → β} (hf : IsUniformInducing f) :
    IsUniformInducing (f '' ·) := by
  constructor
  change Filter.comap _ (Filter.lift' _ _) = Filter.lift' _ _
  rw [Filter.comap_lift'_eq, ← hf.comap_uniformity,
    Filter.comap_lift'_eq2 monotone_hausdorffEntourage]
  congr with U ⟨s, t⟩
  simp only [Function.comp, hausdorffEntourage, SetRel.preimage, SetRel.image, Set.preimage,
    Set.mem_setOf, Set.image_subset_iff, Set.exists_mem_image]

/-- When `Set` is equipped with the Hausdorff uniformity, taking the image under a uniform
embedding is a uniform embedding. -/
theorem IsUniformEmbedding.image_hausdorff {f : α → β} (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (f '' ·) where
  __ := hf.isUniformInducing.image_hausdorff
  injective := hf.injective.image_injective

namespace TopologicalSpace.Closeds

instance uniformSpace : UniformSpace (Closeds α) :=
  .comap (↑) (.hausdorff α)

theorem uniformity_def :
    𝓤 (Closeds α) = .comap (Prod.map (↑) (↑)) ((𝓤 α).lift' hausdorffEntourage) :=
  rfl

theorem _root_.Filter.HasBasis.uniformity_closeds
    {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (Closeds α)).HasBasis p (fun i => Prod.map (↑) (↑) ⁻¹' (hausdorffEntourage (s i))) :=
  h.uniformity_hausdorff.comap _

theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Closeds α → Set α) where
  injective := SetLike.coe_injective
  comap_uniformity := rfl

theorem uniformContinuous_coe : UniformContinuous ((↑) : Closeds α → Set α) :=
  isUniformEmbedding_coe.uniformContinuous

theorem isOpen_inter_nonempty_of_isOpen {s : Set α} (hs : IsOpen s) :
    IsOpen {t : Closeds α | ((t : Set α) ∩ s).Nonempty} :=
  isOpen_induced (UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen hs)

theorem isClosed_subsets_of_isClosed {s : Set α} (hs : IsClosed s) :
    IsClosed {t : Closeds α | (t : Set α) ⊆ s} :=
  isClosed_induced (UniformSpace.hausdorff.isClosed_powerset hs)

section T0Space

variable [T0Space α]

theorem isUniformEmbedding_singleton : IsUniformEmbedding (Closeds.singleton (α := α)) :=
  isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

theorem uniformContinuous_singleton : UniformContinuous (Closeds.singleton (α := α)) :=
  isUniformEmbedding_singleton.uniformContinuous

@[fun_prop]
theorem isEmbedding_singleton : IsEmbedding (Closeds.singleton (α := α)) :=
  isUniformEmbedding_singleton.isEmbedding

@[fun_prop]
theorem continuous_singleton : Continuous (Closeds.singleton (α := α)) :=
  isEmbedding_singleton.continuous

@[fun_prop]
theorem isClosedEmbedding_singleton :
    Topology.IsClosedEmbedding (Closeds.singleton (α := α)) where
  __ := isUniformEmbedding_singleton.isEmbedding
  isClosed_range := by
    rw [← SetLike.coe_injective.preimage_image (s := Set.range singleton), ← Set.range_comp]
    exact UniformSpace.hausdorff.isClosedEmbedding_singleton.isClosed_range.preimage
      uniformContinuous_coe.continuous

end T0Space

end TopologicalSpace.Closeds

namespace TopologicalSpace.Compacts

instance uniformSpace : UniformSpace (Compacts α) :=
  .comap (↑) (.hausdorff α)

theorem uniformity_def :
    𝓤 (Compacts α) = .comap (Prod.map (↑) (↑)) ((𝓤 α).lift' hausdorffEntourage) :=
  rfl

theorem _root_.Filter.HasBasis.uniformity_compacts
    {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (Compacts α)).HasBasis p (fun i => Prod.map (↑) (↑) ⁻¹' (hausdorffEntourage (s i))) :=
  h.uniformity_hausdorff.comap _

theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : Compacts α → Set α) where
  injective := SetLike.coe_injective
  comap_uniformity := rfl

theorem uniformContinuous_coe : UniformContinuous ((↑) : Compacts α → Set α) :=
  isUniformEmbedding_coe.uniformContinuous

theorem isUniformEmbedding_toCloseds [T2Space α] : IsUniformEmbedding (toCloseds (α := α)) where
  injective := toCloseds_injective
  comap_uniformity := Filter.comap_comap

theorem uniformContinuous_toCloseds [T2Space α] : UniformContinuous (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.uniformContinuous

@[fun_prop]
theorem isEmbedding_toCloseds [T2Space α] : IsEmbedding (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.isEmbedding

@[fun_prop]
theorem continuous_toCloseds [T2Space α] : Continuous (toCloseds (α := α)) :=
  uniformContinuous_toCloseds.continuous

theorem isOpen_inter_nonempty_of_isOpen {s : Set α} (hs : IsOpen s) :
    IsOpen {t : Compacts α | ((t : Set α) ∩ s).Nonempty} :=
  isOpen_induced (UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen hs)

theorem isClosed_subsets_of_isClosed {s : Set α} (hs : IsClosed s) :
    IsClosed {t : Compacts α | (t : Set α) ⊆ s} :=
  isClosed_induced (UniformSpace.hausdorff.isClosed_powerset hs)

theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α → Compacts α) :=
  isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

theorem uniformContinuous_singleton : UniformContinuous ({·} : α → Compacts α) :=
  isUniformEmbedding_singleton.uniformContinuous

theorem _root_.UniformContinuous.compacts_map {f : α → β} (hf : UniformContinuous f) :
    UniformContinuous (Compacts.map f hf.continuous) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <| hf.image_hausdorff.comp uniformContinuous_coe

theorem _root_.IsUniformInducing.compacts_map {f : α → β} (hf : IsUniformInducing f) :
    IsUniformInducing (Compacts.map f hf.uniformContinuous.continuous) :=
  .of_comp hf.uniformContinuous.compacts_map uniformContinuous_coe <|
    hf.image_hausdorff.comp isUniformEmbedding_coe.isUniformInducing

theorem _root_.IsUniformEmbedding.compacts_map {f : α → β} (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (Compacts.map f hf.uniformContinuous.continuous) where
  __ := hf.isUniformInducing.compacts_map
  injective := map_injective hf.uniformContinuous.continuous hf.injective

end TopologicalSpace.Compacts

namespace TopologicalSpace.NonemptyCompacts

instance uniformSpace : UniformSpace (NonemptyCompacts α) :=
  .comap (↑) (.hausdorff α)

theorem uniformity_def :
    𝓤 (NonemptyCompacts α) = .comap (Prod.map (↑) (↑)) ((𝓤 α).lift' hausdorffEntourage) :=
  rfl

theorem _root_.Filter.HasBasis.uniformity_nonemptyCompacts
    {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)} (h : (𝓤 α).HasBasis p s) :
    (𝓤 (NonemptyCompacts α)).HasBasis p
      (fun i => Prod.map (↑) (↑) ⁻¹' (hausdorffEntourage (s i))) :=
  h.uniformity_hausdorff.comap _

theorem isUniformEmbedding_coe : IsUniformEmbedding ((↑) : NonemptyCompacts α → Set α) where
  injective := SetLike.coe_injective
  comap_uniformity := rfl

theorem uniformContinuous_coe : UniformContinuous ((↑) : NonemptyCompacts α → Set α) :=
  isUniformEmbedding_coe.uniformContinuous

theorem isUniformEmbedding_toCloseds [T2Space α] : IsUniformEmbedding (toCloseds (α := α)) where
  injective := toCloseds_injective
  comap_uniformity := Filter.comap_comap

theorem uniformContinuous_toCloseds [T2Space α] : UniformContinuous (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.uniformContinuous

@[fun_prop]
theorem isEmbedding_toCloseds [T2Space α] : IsEmbedding (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.isEmbedding

@[fun_prop]
theorem continuous_toCloseds [T2Space α] : Continuous (toCloseds (α := α)) :=
  uniformContinuous_toCloseds.continuous

theorem isUniformEmbedding_toCompacts : IsUniformEmbedding (toCompacts (α := α)) where
  injective := toCompacts_injective
  comap_uniformity := Filter.comap_comap

theorem uniformContinuous_toCompacts : UniformContinuous (toCompacts (α := α)) :=
  isUniformEmbedding_toCompacts.uniformContinuous

@[fun_prop]
theorem isEmbedding_toCompacts : IsEmbedding (toCompacts (α := α)) :=
  isUniformEmbedding_toCompacts.isEmbedding

@[fun_prop]
theorem continuous_toCompacts : Continuous (toCompacts (α := α)) :=
  uniformContinuous_toCompacts.continuous

theorem isOpen_inter_nonempty_of_isOpen {s : Set α} (hs : IsOpen s) :
    IsOpen {t : NonemptyCompacts α | ((t : Set α) ∩ s).Nonempty} :=
  isOpen_induced (UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen hs)

theorem isClosed_subsets_of_isClosed {s : Set α} (hs : IsClosed s) :
    IsClosed {t : NonemptyCompacts α | (t : Set α) ⊆ s} :=
  isClosed_induced (UniformSpace.hausdorff.isClosed_powerset hs)

theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α → NonemptyCompacts α) :=
  isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

theorem uniformContinuous_singleton : UniformContinuous ({·} : α → NonemptyCompacts α) :=
  isUniformEmbedding_singleton.uniformContinuous

theorem _root_.UniformContinuous.nonemptyCompacts_map {f : α → β} (hf : UniformContinuous f) :
    UniformContinuous (NonemptyCompacts.map f hf.continuous) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <| hf.image_hausdorff.comp uniformContinuous_coe

theorem _root_.IsUniformInducing.nonemptyCompacts_map {f : α → β} (hf : IsUniformInducing f) :
    IsUniformInducing (NonemptyCompacts.map f hf.uniformContinuous.continuous) :=
  .of_comp hf.uniformContinuous.nonemptyCompacts_map uniformContinuous_coe <|
    hf.image_hausdorff.comp isUniformEmbedding_coe.isUniformInducing

theorem _root_.IsUniformEmbedding.nonemptyCompacts_map {f : α → β} (hf : IsUniformEmbedding f) :
    IsUniformEmbedding (NonemptyCompacts.map f hf.uniformContinuous.continuous) where
  __ := hf.isUniformInducing.nonemptyCompacts_map
  injective := map_injective hf.uniformContinuous.continuous hf.injective

end TopologicalSpace.NonemptyCompacts
