/-
Copyright (c) 2025 Attila Gáspár. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Attila Gáspár
-/
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Hausdorff uniformity

This file defines the Hausdorff uniformity on the types of closed subsets, compact subsets and
and nonempty compact subsets of a uniform space. This is the generalization of the uniformity
induced by the Hausdorff metric to hyperspaces of uniform spaces.
-/

open UniformSpace
open scoped Uniformity

section

variable {α : Type*} {S : Type*} [SetLike S α]

/-- The set of pairs of sets contained in each other's thickening with respect to an entourage.
These are the generators of the Hausdorff uniformity. -/
def hausdorffEntourage (U : Set (α × α)) : Set (S × S) :=
  {x | ↑x.1 ⊆ thickening U x.2 ∧ ↑x.2 ⊆ thickening U x.1}

theorem isSymmetricRel_hausdorffEntourage (U : Set (α × α)) :
    IsSymmetricRel (hausdorffEntourage (S := S) U) :=
  Set.ext fun _ => And.comm

theorem refl_mem_hausdorffEntourage {U : Set (α × α)} (hU : ∀ x, (x, x) ∈ U) (s : S) :
    (s, s) ∈ hausdorffEntourage U :=
  ⟨self_subset_thickening_of_refl _ fun x _ => hU x,
    self_subset_thickening_of_refl _ fun x _ => hU x⟩

@[gcongr]
theorem hausdorffEntourage_mono {U V : Set (α × α)} (h : U ⊆ V) :
    hausdorffEntourage (S := S) U ⊆ hausdorffEntourage V := by
  unfold hausdorffEntourage
  gcongr

theorem monotone_hausdorffEntourage : Monotone (hausdorffEntourage (S := S)) :=
  fun _ _ => hausdorffEntourage_mono

namespace UniformSpace

variable [UniformSpace α]

/-- The Hausdorff uniformity on a family of subsets of a uniform space.
See note [reducible non-instances]. -/
protected abbrev hausdorff : UniformSpace S := .ofCore
  { uniformity := (𝓤 α).lift' hausdorffEntourage
    refl := by
      simp_rw [Filter.principal_le_lift', idRel_subset]
      exact fun U hU => refl_mem_hausdorffEntourage fun _ => refl_mem_uniformity hU
    symm := by
      rw [Filter.tendsto_lift']
      intro U hU
      filter_upwards [Filter.mem_lift' hU] with _ _
      rwa [← Set.mem_preimage, isSymmetricRel_hausdorffEntourage]
    comp := by
      rw [Filter.le_lift']
      intro U hU
      obtain ⟨V, hV₁, hV₂⟩ := comp_mem_uniformity_sets hU
      refine Filter.mem_of_superset (Filter.mem_lift' (Filter.mem_lift' hV₁)) ?_
      intro ⟨s, u⟩ ⟨t, ⟨hst, hts⟩, ⟨htu, hut⟩⟩
      dsimp only at *
      grw [hts, thickening_thickening_subset, hV₂] at hut
      grw [htu, thickening_thickening_subset, hV₂] at hst
      exact ⟨hst, hut⟩ }

theorem hausdorff.isClosed_disjoint_of_isOpen
    [t : UniformSpace S] (ht : t = .hausdorff) {U : Set α} (hU : IsOpen U) :
    IsClosed {s : S | Disjoint (s : Set α) U} := by
  simp_rw [← isOpen_compl_iff, isOpen_iff_mem_nhds, Set.compl_setOf, Set.not_disjoint_iff]
  intro s ⟨x, hx₁, hx₂⟩
  rw [← hU.mem_nhds_iff, mem_nhds_iff_symm] at hx₂
  obtain ⟨V, hV₁, hV₂, hV₃⟩ := hx₂
  rw [mem_nhds_iff]
  subst t
  refine ⟨_, Filter.mem_lift' hV₁, ?_⟩
  rintro s' ⟨hs', -⟩
  obtain ⟨y, hy₁, hy₂⟩ := Set.mem_iUnion₂.mp <| hs' hx₁
  rw [mem_ball_symmetry hV₂] at hy₂
  exact ⟨y, hy₁, hV₃ hy₂⟩

theorem hausdorff.isClosed_subsets_of_isClosed
    [t : UniformSpace S] (ht : t = .hausdorff) {F : Set α} (hF : IsClosed F) :
    IsClosed {s : S | (s : Set α) ⊆ F} := by
  simp_rw [← Set.disjoint_compl_right_iff_subset]
  exact isClosed_disjoint_of_isOpen ht hF.isOpen_compl

end UniformSpace

end

variable {α : Type*} [UniformSpace α]

namespace TopologicalSpace.Closeds

instance uniformSpace : UniformSpace (Closeds α) :=
  .hausdorff

theorem uniformity_def : 𝓤 (Closeds α) = (𝓤 α).lift' hausdorffEntourage :=
  rfl

theorem _root_.Filter.HasBasis.uniformity_closeds
    {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) : (𝓤 (Closeds α)).HasBasis p (hausdorffEntourage ∘ s) :=
  h.lift' monotone_hausdorffEntourage

theorem isClosed_disjoint_of_isOpen {s : Set α} (hs : IsOpen s) :
    IsClosed {t : Closeds α | Disjoint (t : Set α) s} :=
  hausdorff.isClosed_disjoint_of_isOpen rfl hs

theorem isClosed_subsets_of_isClosed {s : Set α} (hs : IsClosed s) :
    IsClosed {t : Closeds α | (t : Set α) ⊆ s} :=
  hausdorff.isClosed_subsets_of_isClosed rfl hs

end TopologicalSpace.Closeds

namespace TopologicalSpace.Compacts

instance uniformSpace : UniformSpace (Compacts α) :=
  .hausdorff

theorem uniformity_def : 𝓤 (Compacts α) = (𝓤 α).lift' hausdorffEntourage :=
  rfl

theorem _root_.Filter.HasBasis.uniformity_compacts
    {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) : (𝓤 (Compacts α)).HasBasis p (hausdorffEntourage ∘ s) :=
  h.lift' monotone_hausdorffEntourage

theorem isClosed_disjoint_of_isOpen {s : Set α} (hs : IsOpen s) :
    IsClosed {t : Compacts α | Disjoint (t : Set α) s} :=
  hausdorff.isClosed_disjoint_of_isOpen rfl hs

theorem isClosed_subsets_of_isClosed {s : Set α} (hs : IsClosed s) :
    IsClosed {t : Compacts α | (t : Set α) ⊆ s} :=
  hausdorff.isClosed_subsets_of_isClosed rfl hs

end TopologicalSpace.Compacts

namespace TopologicalSpace.NonemptyCompacts

instance uniformSpace : UniformSpace (NonemptyCompacts α) :=
  .hausdorff

theorem uniformity_def : 𝓤 (NonemptyCompacts α) = (𝓤 α).lift' hausdorffEntourage :=
  rfl

theorem _root_.Filter.HasBasis.uniformity_nonemptyCompacts
    {ι : Sort*} {p : ι → Prop} {s : ι → Set (α × α)}
    (h : (𝓤 α).HasBasis p s) : (𝓤 (NonemptyCompacts α)).HasBasis p (hausdorffEntourage ∘ s) :=
  h.lift' monotone_hausdorffEntourage

theorem isUniformEmbedding_toCloseds [T2Space α] :
    IsUniformEmbedding (toCloseds (α := α)) where
  injective := toCloseds_injective
  comap_uniformity := Filter.comap_lift'_eq

theorem continuous_toCloseds [T2Space α] :
    Continuous (toCloseds (α := α)) :=
  isUniformEmbedding_toCloseds.uniformContinuous.continuous

theorem isUniformEmbedding_toCompacts :
    IsUniformEmbedding (toCompacts (α := α)) where
  injective := toCompacts_injective
  comap_uniformity := Filter.comap_lift'_eq

theorem continuous_toCompacts :
    Continuous (toCompacts (α := α)) :=
  isUniformEmbedding_toCompacts.uniformContinuous.continuous

theorem isClosed_disjoint_of_isOpen {s : Set α} (hs : IsOpen s) :
    IsClosed {t : NonemptyCompacts α | Disjoint (t : Set α) s} :=
  hausdorff.isClosed_disjoint_of_isOpen rfl hs

theorem isClosed_subsets_of_isClosed {s : Set α} (hs : IsClosed s) :
    IsClosed {t : NonemptyCompacts α | (t : Set α) ⊆ s} :=
  hausdorff.isClosed_subsets_of_isClosed rfl hs

end TopologicalSpace.NonemptyCompacts
