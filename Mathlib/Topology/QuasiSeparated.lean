/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Separation
import Mathlib.Topology.NoetherianSpace

#align_import topology.quasi_separated from "leanprover-community/mathlib"@"5dc6092d09e5e489106865241986f7f2ad28d4c8"

/-!
# Quasi-separated spaces

A topological space is quasi-separated if the intersections of any pairs of compact open subsets
are still compact.
Notable examples include spectral spaces, Noetherian spaces, and Hausdorff spaces.

A non-example is the interval `[0, 1]` with doubled origin: the two copies of `[0, 1]` are compact
open subsets, but their intersection `(0, 1]` is not.

## Main results

- `IsQuasiSeparated`: A subset `s` of a topological space is quasi-separated if the intersections
of any pairs of compact open subsets of `s` are still compact.
- `QuasiSeparatedSpace`: A topological space is quasi-separated if the intersections of any pairs
of compact open subsets are still compact.
- `QuasiSeparatedSpace.of_openEmbedding`: If `f : α → β` is an open embedding, and `β` is
  a quasi-separated space, then so is `α`.
-/


open TopologicalSpace

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}

/-- A subset `s` of a topological space is quasi-separated if the intersections of any pairs of
compact open subsets of `s` are still compact.

Note that this is equivalent to `s` being a `QuasiSeparatedSpace` only when `s` is open. -/
def IsQuasiSeparated (s : Set α) : Prop :=
  ∀ U V : Set α, U ⊆ s → IsOpen U → IsCompact U → V ⊆ s → IsOpen V → IsCompact V → IsCompact (U ∩ V)
#align is_quasi_separated IsQuasiSeparated

/-- A topological space is quasi-separated if the intersections of any pairs of compact open
subsets are still compact. -/
@[mk_iff]
class QuasiSeparatedSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- The intersection of two open compact subsets of a quasi-separated space is compact. -/
  inter_isCompact :
    ∀ U V : Set α, IsOpen U → IsCompact U → IsOpen V → IsCompact V → IsCompact (U ∩ V)
#align quasi_separated_space QuasiSeparatedSpace

theorem isQuasiSeparated_univ_iff {α : Type*} [TopologicalSpace α] :
    IsQuasiSeparated (Set.univ : Set α) ↔ QuasiSeparatedSpace α := by
  rw [quasiSeparatedSpace_iff]
  simp [IsQuasiSeparated]
#align is_quasi_separated_univ_iff isQuasiSeparated_univ_iff

theorem isQuasiSeparated_univ {α : Type*} [TopologicalSpace α] [QuasiSeparatedSpace α] :
    IsQuasiSeparated (Set.univ : Set α) :=
  isQuasiSeparated_univ_iff.mpr inferInstance
#align is_quasi_separated_univ isQuasiSeparated_univ

theorem IsQuasiSeparated.image_of_embedding {s : Set α} (H : IsQuasiSeparated s) (h : Embedding f) :
    IsQuasiSeparated (f '' s) := by
  intro U V hU hU' hU'' hV hV' hV''
  convert
    (H (f ⁻¹' U) (f ⁻¹' V)
      ?_ (h.continuous.1 _ hU') ?_ ?_ (h.continuous.1 _ hV') ?_).image h.continuous
  · symm
    rw [← Set.preimage_inter, Set.image_preimage_eq_inter_range, Set.inter_eq_left]
    exact Set.inter_subset_left.trans (hU.trans (Set.image_subset_range _ _))
  · intro x hx
    rw [← h.inj.injOn.mem_image_iff (Set.subset_univ _) trivial]
    exact hU hx
  · rw [h.isCompact_iff]
    convert hU''
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left]
    exact hU.trans (Set.image_subset_range _ _)
  · intro x hx
    rw [← h.inj.injOn.mem_image_iff (Set.subset_univ _) trivial]
    exact hV hx
  · rw [h.isCompact_iff]
    convert hV''
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left]
    exact hV.trans (Set.image_subset_range _ _)
#align is_quasi_separated.image_of_embedding IsQuasiSeparated.image_of_embedding

theorem OpenEmbedding.isQuasiSeparated_iff (h : OpenEmbedding f) {s : Set α} :
    IsQuasiSeparated s ↔ IsQuasiSeparated (f '' s) := by
  refine ⟨fun hs => hs.image_of_embedding h.toEmbedding, ?_⟩
  intro H U V hU hU' hU'' hV hV' hV''
  rw [h.toEmbedding.isCompact_iff, Set.image_inter h.inj]
  exact
    H (f '' U) (f '' V) (Set.image_subset _ hU) (h.isOpenMap _ hU') (hU''.image h.continuous)
      (Set.image_subset _ hV) (h.isOpenMap _ hV') (hV''.image h.continuous)
#align open_embedding.is_quasi_separated_iff OpenEmbedding.isQuasiSeparated_iff

theorem isQuasiSeparated_iff_quasiSeparatedSpace (s : Set α) (hs : IsOpen s) :
    IsQuasiSeparated s ↔ QuasiSeparatedSpace s := by
  rw [← isQuasiSeparated_univ_iff]
  convert (hs.openEmbedding_subtype_val.isQuasiSeparated_iff (s := Set.univ)).symm
  simp
#align is_quasi_separated_iff_quasi_separated_space isQuasiSeparated_iff_quasiSeparatedSpace

theorem IsQuasiSeparated.of_subset {s t : Set α} (ht : IsQuasiSeparated t) (h : s ⊆ t) :
    IsQuasiSeparated s := by
  intro U V hU hU' hU'' hV hV' hV''
  exact ht U V (hU.trans h) hU' hU'' (hV.trans h) hV' hV''
#align is_quasi_separated.of_subset IsQuasiSeparated.of_subset

instance (priority := 100) T2Space.to_quasiSeparatedSpace [T2Space α] : QuasiSeparatedSpace α :=
  ⟨fun _ _ _ hU' _ hV' => hU'.inter hV'⟩
#align t2_space.to_quasi_separated_space T2Space.to_quasiSeparatedSpace

instance (priority := 100) NoetherianSpace.to_quasiSeparatedSpace [NoetherianSpace α] :
    QuasiSeparatedSpace α :=
  ⟨fun _ _ _ _ _ _ => NoetherianSpace.isCompact _⟩
#align noetherian_space.to_quasi_separated_space NoetherianSpace.to_quasiSeparatedSpace

theorem IsQuasiSeparated.of_quasiSeparatedSpace (s : Set α) [QuasiSeparatedSpace α] :
    IsQuasiSeparated s :=
  isQuasiSeparated_univ.of_subset (Set.subset_univ _)
#align is_quasi_separated.of_quasi_separated_space IsQuasiSeparated.of_quasiSeparatedSpace

theorem QuasiSeparatedSpace.of_openEmbedding (h : OpenEmbedding f) [QuasiSeparatedSpace β] :
    QuasiSeparatedSpace α :=
  isQuasiSeparated_univ_iff.mp
    (h.isQuasiSeparated_iff.mpr <| IsQuasiSeparated.of_quasiSeparatedSpace _)
#align quasi_separated_space.of_open_embedding QuasiSeparatedSpace.of_openEmbedding
