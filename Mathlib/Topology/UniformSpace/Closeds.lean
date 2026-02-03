/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

public import Mathlib.Topology.Order.Lattice
public import Mathlib.Topology.Sets.VietorisTopology
public import Mathlib.Topology.UniformSpace.UniformEmbedding

import Mathlib.Topology.UniformSpace.Compact

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

@[simp]
theorem hausdorffEntourage_id : hausdorffEntourage (.id : SetRel α α) = .id := by
  simp_rw [hausdorffEntourage, preimage_id, image_id, ← subset_antisymm_iff, SetRel.id]

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

theorem union_mem_hausdorffEntourage (U : SetRel α α) {s₁ s₂ t₁ t₂ : Set α}
    (h₁ : (s₁, t₁) ∈ hausdorffEntourage U) (h₂ : (s₂, t₂) ∈ hausdorffEntourage U) :
    (s₁ ∪ s₂, t₁ ∪ t₂) ∈ hausdorffEntourage U := by
  grind [mem_hausdorffEntourage, preimage_union, image_union]

theorem TotallyBounded.exists_prodMk_finset_mem_hausdorffEntourage [UniformSpace α]
    {s : Set α} (hs : TotallyBounded s) {U : SetRel α α} (hU : U ∈ 𝓤 α) :
    ∃ t : Finset α, (↑t, s) ∈ hausdorffEntourage U := by
  obtain ⟨t, ht₁, ht₂⟩ := hs _ (symm_le_uniformity hU)
  lift t to Finset α using ht₁
  classical
  refine ⟨{x ∈ t | ∃ y ∈ s, (x, y) ∈ U}, ?_⟩
  rw [Finset.coe_filter]
  refine ⟨fun _ h => h.2, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht₂ hx)
  exact ⟨y, ⟨hy, x, hx, hxy⟩, hxy⟩

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
      have := isRefl_of_mem_uniformity hU
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

/-- In the Hausdorff uniformity, the powerset of a closed set is closed. -/
theorem _root_.IsClosed.powerset_hausdorff {F : Set α} (hF : IsClosed F) :
    IsClosed F.powerset := by
  simp_rw [Set.powerset, ← isOpen_compl_iff, Set.compl_setOf, ← Set.inter_compl_nonempty_iff]
  exact isOpen_inter_nonempty_of_isOpen hF.isOpen_compl

@[deprecated (since := "2025-11-23")] alias isClosed_powerset := IsClosed.powerset_hausdorff

theorem isClopen_singleton_empty : IsClopen {(∅ : Set α)} := by
  constructor
  · rw [← Set.powerset_empty]
    exact isClosed_empty.powerset_hausdorff
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

theorem uniformContinuous_union : UniformContinuous (fun x : Set α × Set α => x.1 ∪ x.2) := by
  refine Filter.tendsto_lift'.mpr fun U hU => ?_
  filter_upwards [entourageProd_mem_uniformity (Filter.mem_lift' hU) (Filter.mem_lift' hU)]
    with _ ⟨h₁, h₂⟩ using union_mem_hausdorffEntourage U h₁ h₂

theorem uniformContinuous_closure : UniformContinuous (closure (X := α)) := by
  simp_rw [UniformContinuous, (𝓤 α).basis_sets.uniformity_hausdorff.tendsto_iff
    (𝓤 α).basis_sets.uniformity_hausdorff, Function.comp_id, mem_hausdorffEntourage]
  intro U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  refine ⟨V, hV, fun ⟨s, t⟩ ⟨hst, hts⟩ => ?_⟩
  simp only at *
  constructor
  · grw [closure_subset_preimage hV s, hst, ← subset_closure, ← hVU, SetRel.preimage_comp]
  · grw [closure_subset_image hV t, hts, ← subset_closure, ← hVU, SetRel.image_comp]

@[fun_prop]
theorem continuous_closure : Continuous (closure (X := α)) :=
  uniformContinuous_closure.continuous

theorem isUniformInducing_closure : IsUniformInducing (closure (X := α)) := by
  refine ⟨le_antisymm ?_ <| Filter.map_le_iff_le_comap.mp uniformContinuous_closure⟩
  rw [(𝓤 α).basis_sets.uniformity_hausdorff.comap _ |>.le_basis_iff
    (𝓤 α).basis_sets.uniformity_hausdorff, Function.comp_id]
  intro U hU
  obtain ⟨V : SetRel α α, hV, hVU⟩ := comp_mem_uniformity_sets hU
  refine ⟨V, hV, fun ⟨s, t⟩ ⟨hst, hts⟩ => ?_⟩
  simp only [mem_hausdorffEntourage] at *
  constructor
  · grw [subset_closure (s := s), hst, closure_subset_preimage hV t, ← hVU, SetRel.preimage_comp]
  · grw [subset_closure (s := t), hts, closure_subset_image hV s, ← hVU, SetRel.image_comp]

theorem nhds_closure (s : Set α) : 𝓝 (closure s) = 𝓝 s := by
  simp_rw +singlePass [isUniformInducing_closure.isInducing.nhds_eq_comap, closure_closure]

instance [DiscreteUniformity α] : DiscreteUniformity (Set α) := by
  rw [discreteUniformity_iff_setRelId_mem_uniformity]
  convert Filter.mem_lift' (DiscreteUniformity.relId_mem_uniformity α)
  rw [hausdorffEntourage_id]

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

/-- In the Hausdorff uniformity, the powerset of a totally bounded set is totally bounded. -/
theorem TotallyBounded.powerset_hausdorff {t : Set α} (ht : TotallyBounded t) :
    TotallyBounded t.powerset := by
  simp_rw [(𝓤 α).basis_sets.uniformity_hausdorff.totallyBounded_iff, Function.comp_id,
    Set.powerset, Set.setOf_subset, Set.mem_iUnion]
  intro (U : SetRel α α) hU
  obtain ⟨u, hu, ht⟩ := ht U hU
  refine ⟨u.powerset, hu.powerset, fun s hs => ⟨u ∩ U.image s, by grind, fun x hx => ?_,
    fun x ⟨_, hx⟩ => hx⟩⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (ht (hs hx))
  exact ⟨y, ⟨hy, ⟨x, hx, hxy⟩⟩, hxy⟩

/-- The neighborhoods of a totally bounded set in the Hausdorff uniformity are neighborhoods in the
Vietoris topology. -/
theorem TotallyBounded.nhds_vietoris_le_nhds_hausdorff {s : Set α} (hs : TotallyBounded s) :
    @nhds _ (.vietoris α) s ≤ 𝓝 s := by
  open UniformSpace TopologicalSpace.vietoris in
  simp_rw [nhds_eq_comap_uniformity,
    uniformity_hasBasis_open.uniformity_hausdorff |>.comap _ |>.ge_iff, Function.comp_id,
    hausdorffEntourage, Set.preimage_setOf_eq, Set.setOf_and]
  intro U ⟨hU₁, hU₂⟩
  have : U.IsRefl := ⟨fun _ => refl_mem_uniformity hU₁⟩
  let := TopologicalSpace.vietoris α
  refine Filter.inter_mem ?_ <| hU₂.relImage.powerset_vietoris.mem_nhds <|
    SetRel.self_subset_image _
  obtain ⟨V : SetRel α α, hV₁, hV₂, _, hVU⟩ := comp_open_symm_mem_uniformity_sets hU₁
  obtain ⟨t, ht₁, ht₂⟩ := hs.exists_prodMk_finset_mem_hausdorffEntourage hV₁
  dsimp only at ht₁ ht₂
  filter_upwards [(Filter.eventually_all_finset t).mpr fun x hx =>
    isOpen_inter_nonempty_of_isOpen (isOpen_ball x hV₂) |>.eventually_mem (ht₁ hx)]
    with u (hu : ↑t ⊆ V.preimage ↑u)
  grw [ht₂, ← SetRel.preimage_eq_image, hu, ← hVU, SetRel.preimage_comp]

/-- A compact set has the same neighborhoods in the Hausdorff uniformity and the Vietoris topology.
-/
theorem IsCompact.nhds_hausdorff_eq_nhds_vietoris {s : Set α} (hs : IsCompact s) :
    𝓝 s = @nhds _ (.vietoris α) s := by
  refine le_antisymm ?_ hs.totallyBounded.nhds_vietoris_le_nhds_hausdorff
  simp_rw [TopologicalSpace.nhds_generateFrom, le_iInf₂_iff, Filter.le_principal_iff]
  rintro _ ⟨hs', (⟨U, hU, rfl⟩ | ⟨U, hU, rfl⟩)⟩
  · obtain ⟨V : SetRel α α, hV₁, hV₂⟩ :=
      hs.nhdsSet_basis_uniformity (𝓤 α).basis_sets |>.mem_iff.mp (hU.mem_nhdsSet.mpr hs')
    filter_upwards [UniformSpace.ball_mem_nhds _ (Filter.mem_lift' hV₁)]
      with t ⟨_, ht⟩
    exact ht.trans fun x ⟨y, hy, hxy⟩ => hV₂ <| Set.mem_biUnion hy hxy
  · exact (UniformSpace.hausdorff.isOpen_inter_nonempty_of_isOpen hU).mem_nhds hs'

namespace UniformSpace.hausdorff

instance [CompactSpace α] : CompactSpace (Set α) where
  isCompact_univ := by
    rw [isCompact_iff_ultrafilter_le_nhds]
    rintro f -
    let := TopologicalSpace.vietoris α
    -- `f.lim` is the limit of `f` in the Vietoris topology
    refine ⟨closure f.lim, Set.mem_univ _, ?_⟩
    grw [isClosed_closure.isCompact.nhds_hausdorff_eq_nhds_vietoris,
      ← TopologicalSpace.vietoris.specializes_closure.nhds_le_nhds, f.le_nhds_lim]

end UniformSpace.hausdorff

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
  isClosed_induced hs.powerset_hausdorff

theorem isClopen_singleton_bot : IsClopen {(⊥ : Closeds α)} := by
  convert UniformSpace.hausdorff.isClopen_singleton_empty.preimage
    uniformContinuous_coe.continuous
  ext; simp

theorem totallyBounded_subsets_of_totallyBounded {t : Set α} (ht : TotallyBounded t) :
    TotallyBounded {F : Closeds α | ↑F ⊆ t} :=
  totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff

instance [DiscreteUniformity α] : DiscreteUniformity (Closeds α) :=
  isUniformEmbedding_coe.discreteUniformity

section T0Space

variable [T0Space α]

theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α → Closeds α) :=
  isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

theorem uniformContinuous_singleton : UniformContinuous ({·} : α → Closeds α) :=
  isUniformEmbedding_singleton.uniformContinuous

@[fun_prop]
theorem isEmbedding_singleton : IsEmbedding ({·} : α → Closeds α) :=
  isUniformEmbedding_singleton.isEmbedding

@[fun_prop]
theorem continuous_singleton : Continuous ({·} : α → Closeds α) :=
  isEmbedding_singleton.continuous

@[fun_prop]
theorem isClosedEmbedding_singleton : Topology.IsClosedEmbedding ({·} : α → Closeds α) where
  __ := isUniformEmbedding_singleton.isEmbedding
  isClosed_range := by
    rw [← SetLike.coe_injective.preimage_image (s := Set.range ({·})), ← Set.range_comp]
    exact UniformSpace.hausdorff.isClosedEmbedding_singleton.isClosed_range.preimage
      uniformContinuous_coe.continuous

@[simp]
theorem discreteUniformity_iff : DiscreteUniformity (Closeds α) ↔ DiscreteUniformity α :=
  ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

end T0Space

theorem uniformContinuous_sup : UniformContinuous (fun x : Closeds α × Closeds α => x.1 ⊔ x.2) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <|
    UniformSpace.hausdorff.uniformContinuous_union.comp <|
      uniformContinuous_coe.prodMap uniformContinuous_coe

theorem _root_.UniformContinuous.sup_closeds
    {f g : α → Closeds β} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ⊔ g x) :=
  uniformContinuous_sup.comp <| hf.prodMk hg

instance : ContinuousSup (Closeds α) :=
  ⟨uniformContinuous_sup.continuous⟩

instance : T0Space (Closeds α) := by
  suffices ∀ F₁ F₂ : Closeds α, Inseparable F₁ F₂ → F₁ ≤ F₂ from
    ⟨fun F₁ F₂ h => le_antisymm (this F₁ F₂ h) (this F₂ F₁ h.symm)⟩
  refine fun F₁ F₂ h x hx₁ => isClosed_iff_frequently.mp F₂.isClosed _ ?_
  rw [nhds_eq_comap_uniformity, Filter.frequently_comap, Filter.frequently_iff]
  intro (U : SetRel α α) hU
  obtain ⟨h : (F₁ : Set α) ⊆ U.preimage F₂, -⟩ :=
    mem_of_mem_nhds <| h.nhds_le_uniformity <| Filter.preimage_mem_comap <| Filter.mem_lift' hU
  obtain ⟨y, hy, hxy⟩ := h hx₁
  exact ⟨(x, y), hxy, y, rfl, hy⟩

theorem isUniformInducing_closure : IsUniformInducing (Closeds.closure (α := α)) :=
  isUniformEmbedding_coe.isUniformInducing_comp_iff.mp
    UniformSpace.hausdorff.isUniformInducing_closure

theorem uniformContinuous_closure : UniformContinuous (Closeds.closure (α := α)) :=
  isUniformInducing_closure.uniformContinuous

@[fun_prop]
theorem continuous_closure : Continuous (Closeds.closure (α := α)) :=
  uniformContinuous_closure.continuous

instance [CompactSpace α] : CompactSpace (Closeds α) where
  isCompact_univ := by simpa [gi.l_surjective.range_eq]
    using isCompact_univ.image continuous_closure

@[simp]
theorem compactSpace_iff : CompactSpace (Closeds α) ↔ CompactSpace α := by
  refine ⟨fun _ => compactSpace_of_finite_subfamily_closed fun {ι} F hF₁ hF₂ => ?_,
    fun _ => inferInstance⟩
  have := isClopen_singleton_bot.compl.isClosed.isCompact.elim_finite_subfamily_closed
    (fun i => {C : Closeds α | ↑C ⊆ F i})
    (fun i => isClosed_subsets_of_isClosed (hF₁ i))
  simp_rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_compl_left_iff_subset,
    ← Set.setOf_forall, ← Set.subset_iInter_iff, hF₂, Set.subset_empty_iff, coe_eq_empty,
    Set.setOf_eq_eq_singleton] at this
  obtain ⟨s, hs⟩ := this .rfl
  specialize @hs ⟨⋂ i ∈ s, F i, isClosed_biInter fun i _ => hF₁ i⟩ .rfl
  exact ⟨s, congr($hs)⟩

@[simp]
theorem noncompactSpace_iff : NoncompactSpace (Closeds α) ↔ NoncompactSpace α := by
  simp_rw [← not_compactSpace_iff, compactSpace_iff]

instance [NoncompactSpace α] : NoncompactSpace (Closeds α) :=
  noncompactSpace_iff.mpr ‹_›

end TopologicalSpace.Closeds

namespace TopologicalSpace.Compacts

instance uniformSpace : UniformSpace (Compacts α) :=
  .replaceTopology (.comap (↑) (.hausdorff α)) <| ext_nhds fun K =>  by
    simp_rw [nhds_induced, K.isCompact.nhds_hausdorff_eq_nhds_vietoris]

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

theorem totallyBounded_subsets_of_totallyBounded {t : Set α} (ht : TotallyBounded t) :
    TotallyBounded {K : Compacts α | ↑K ⊆ t} :=
  totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff

theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α → Compacts α) :=
  isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

theorem uniformContinuous_singleton : UniformContinuous ({·} : α → Compacts α) :=
  isUniformEmbedding_singleton.uniformContinuous

theorem uniformContinuous_sup :
    UniformContinuous (fun x : Compacts α × Compacts α => x.1 ⊔ x.2) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <|
    UniformSpace.hausdorff.uniformContinuous_union.comp <|
      uniformContinuous_coe.prodMap uniformContinuous_coe

theorem _root_.UniformContinuous.sup_compacts
    {f g : α → Compacts β} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ⊔ g x) :=
  uniformContinuous_sup.comp <| hf.prodMk hg

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

instance [DiscreteUniformity α] : DiscreteUniformity (Compacts α) :=
  isUniformEmbedding_coe.discreteUniformity

@[simp]
theorem discreteUniformity_iff : DiscreteUniformity (Compacts α) ↔ DiscreteUniformity α :=
  ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

end TopologicalSpace.Compacts

namespace TopologicalSpace.NonemptyCompacts

instance uniformSpace : UniformSpace (NonemptyCompacts α) :=
  .replaceTopology (.comap (↑) (.hausdorff α)) <| ext_nhds fun K =>  by
    simp_rw [nhds_induced, K.isCompact.nhds_hausdorff_eq_nhds_vietoris]

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

theorem totallyBounded_subsets_of_totallyBounded {t : Set α} (ht : TotallyBounded t) :
    TotallyBounded {K : NonemptyCompacts α | ↑K ⊆ t} :=
  totallyBounded_preimage isUniformEmbedding_coe.isUniformInducing ht.powerset_hausdorff

theorem isUniformEmbedding_singleton : IsUniformEmbedding ({·} : α → NonemptyCompacts α) :=
  isUniformEmbedding_coe.of_comp_iff.mp UniformSpace.hausdorff.isUniformEmbedding_singleton

theorem uniformContinuous_singleton : UniformContinuous ({·} : α → NonemptyCompacts α) :=
  isUniformEmbedding_singleton.uniformContinuous

theorem uniformContinuous_sup :
    UniformContinuous (fun x : NonemptyCompacts α × NonemptyCompacts α => x.1 ⊔ x.2) :=
  isUniformEmbedding_coe.uniformContinuous_iff.mpr <|
    UniformSpace.hausdorff.uniformContinuous_union.comp <|
      uniformContinuous_coe.prodMap uniformContinuous_coe

theorem _root_.UniformContinuous.sup_nonemptyCompacts
    {f g : α → NonemptyCompacts β} (hf : UniformContinuous f) (hg : UniformContinuous g) :
    UniformContinuous (fun x => f x ⊔ g x) :=
  uniformContinuous_sup.comp <| hf.prodMk hg

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

instance [DiscreteUniformity α] : DiscreteUniformity (NonemptyCompacts α) :=
  isUniformEmbedding_coe.discreteUniformity

@[simp]
theorem discreteUniformity_iff : DiscreteUniformity (NonemptyCompacts α) ↔ DiscreteUniformity α :=
  ⟨fun _ => isUniformEmbedding_singleton.discreteUniformity, fun _ => inferInstance⟩

end TopologicalSpace.NonemptyCompacts
