/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
module

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

variable {α : Type*}

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

variable [UniformSpace α]

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

end UniformSpace.hausdorff

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
  refine Filter.inter_mem ?_ <| (isOpen_powerset hU₂.relImage).mem_nhds <|
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

end TopologicalSpace.NonemptyCompacts
