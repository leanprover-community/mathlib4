/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Topology.Compactness.Bases
import Mathlib.Topology.NoetherianSpace

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
- `QuasiSeparatedSpace.of_isOpenEmbedding`: If `f : α → β` is an open embedding, and `β` is
  a quasi-separated space, then so is `α`.
-/

open Set TopologicalSpace Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}

/-- A subset `s` of a topological space is quasi-separated if the intersections of any pairs of
compact open subsets of `s` are still compact.

Note that this is equivalent to `s` being a `QuasiSeparatedSpace` only when `s` is open. -/
def IsQuasiSeparated (s : Set α) : Prop :=
  ∀ U V : Set α, U ⊆ s → IsOpen U → IsCompact U → V ⊆ s → IsOpen V → IsCompact V → IsCompact (U ∩ V)

/-- A topological space is quasi-separated if the intersections of any pairs of compact open
subsets are still compact. -/
@[mk_iff]
class QuasiSeparatedSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- The intersection of two open compact subsets of a quasi-separated space is compact. -/
  inter_isCompact :
    ∀ U V : Set α, IsOpen U → IsCompact U → IsOpen V → IsCompact V → IsCompact (U ∩ V)

theorem isQuasiSeparated_univ_iff {α : Type*} [TopologicalSpace α] :
    IsQuasiSeparated (Set.univ : Set α) ↔ QuasiSeparatedSpace α := by
  rw [quasiSeparatedSpace_iff]
  simp [IsQuasiSeparated]

theorem isQuasiSeparated_univ {α : Type*} [TopologicalSpace α] [QuasiSeparatedSpace α] :
    IsQuasiSeparated (Set.univ : Set α) :=
  isQuasiSeparated_univ_iff.mpr inferInstance

theorem IsQuasiSeparated.image_of_isEmbedding {s : Set α} (H : IsQuasiSeparated s)
    (h : IsEmbedding f) : IsQuasiSeparated (f '' s) := by
  intro U V hU hU' hU'' hV hV' hV''
  convert
    (H (f ⁻¹' U) (f ⁻¹' V)
      ?_ (h.continuous.1 _ hU') ?_ ?_ (h.continuous.1 _ hV') ?_).image h.continuous
  · symm
    rw [← Set.preimage_inter, Set.image_preimage_eq_inter_range, Set.inter_eq_left]
    exact Set.inter_subset_left.trans (hU.trans (Set.image_subset_range _ _))
  · intro x hx
    rw [← h.injective.injOn.mem_image_iff (Set.subset_univ _) trivial]
    exact hU hx
  · rw [h.isCompact_iff]
    convert hU''
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left]
    exact hU.trans (Set.image_subset_range _ _)
  · intro x hx
    rw [← h.injective.injOn.mem_image_iff (Set.subset_univ _) trivial]
    exact hV hx
  · rw [h.isCompact_iff]
    convert hV''
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left]
    exact hV.trans (Set.image_subset_range _ _)

theorem Topology.IsOpenEmbedding.isQuasiSeparated_iff (h : IsOpenEmbedding f) {s : Set α} :
    IsQuasiSeparated s ↔ IsQuasiSeparated (f '' s) := by
  refine ⟨fun hs => hs.image_of_isEmbedding h.isEmbedding, ?_⟩
  intro H U V hU hU' hU'' hV hV' hV''
  rw [h.isEmbedding.isCompact_iff, Set.image_inter h.injective]
  exact
    H (f '' U) (f '' V) (image_mono hU) (h.isOpenMap _ hU') (hU''.image h.continuous)
      (image_mono hV) (h.isOpenMap _ hV') (hV''.image h.continuous)

theorem isQuasiSeparated_iff_quasiSeparatedSpace (s : Set α) (hs : IsOpen s) :
    IsQuasiSeparated s ↔ QuasiSeparatedSpace s := by
  rw [← isQuasiSeparated_univ_iff]
  convert (hs.isOpenEmbedding_subtypeVal.isQuasiSeparated_iff (s := Set.univ)).symm
  simp

theorem IsQuasiSeparated.of_subset {s t : Set α} (ht : IsQuasiSeparated t) (h : s ⊆ t) :
    IsQuasiSeparated s := by
  intro U V hU hU' hU'' hV hV' hV''
  exact ht U V (hU.trans h) hU' hU'' (hV.trans h) hV' hV''

instance (priority := 100) T2Space.to_quasiSeparatedSpace [T2Space α] : QuasiSeparatedSpace α :=
  ⟨fun _ _ _ hU' _ hV' => hU'.inter hV'⟩

instance (priority := 100) NoetherianSpace.to_quasiSeparatedSpace [NoetherianSpace α] :
    QuasiSeparatedSpace α :=
  ⟨fun _ _ _ _ _ _ => NoetherianSpace.isCompact _⟩

lemma QuasiSeparatedSpace.of_isTopologicalBasis {ι : Type*} {b : ι → Set α}
    (basis : IsTopologicalBasis (range b)) (isCompact_inter : ∀ i j, IsCompact (b i ∩ b j)) :
    QuasiSeparatedSpace α where
  inter_isCompact U V hUopen hUcomp hVopen hVcomp := by
    have aux := isCompact_open_iff_eq_finite_iUnion_of_isTopologicalBasis b basis fun i ↦ by
      simpa using isCompact_inter i i
    obtain ⟨s, hs, rfl⟩ := (aux _).1 ⟨hUcomp, hUopen⟩
    obtain ⟨t, ht, rfl⟩ := (aux _).1 ⟨hVcomp, hVopen⟩
    rw [iUnion₂_inter_iUnion₂]
    exact hs.isCompact_biUnion fun i hi ↦ ht.isCompact_biUnion fun j hj ↦ isCompact_inter ..

section QuasiSeparatedSpace
variable [QuasiSeparatedSpace α] {U V : Set α}

lemma IsQuasiSeparated.of_quasiSeparatedSpace (s : Set α) : IsQuasiSeparated s :=
  isQuasiSeparated_univ.of_subset (Set.subset_univ _)

lemma QuasiSeparatedSpace.of_isOpenEmbedding {f : β → α} (h : IsOpenEmbedding f) :
    QuasiSeparatedSpace β :=
  isQuasiSeparated_univ_iff.mp (h.isQuasiSeparated_iff.mpr <| .of_quasiSeparatedSpace _)

lemma IsCompact.inter_of_isOpen (hUcomp : IsCompact U) (hVcomp : IsCompact V) (hUopen : IsOpen U)
    (hVopen : IsOpen V) : IsCompact (U ∩ V) :=
  QuasiSeparatedSpace.inter_isCompact _ _ hUopen hUcomp hVopen hVcomp

end QuasiSeparatedSpace

lemma quasiSeparatedSpace_congr (e : α ≃ₜ β) : QuasiSeparatedSpace α ↔ QuasiSeparatedSpace β where
  mp _ := .of_isOpenEmbedding e.symm.isOpenEmbedding
  mpr _ := .of_isOpenEmbedding e.isOpenEmbedding
