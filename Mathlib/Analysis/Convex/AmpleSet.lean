/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Floris van Doorn
-/
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.LinearAlgebra.AffineSpace.ContinuousAffineEquiv

/-!
# Ample subsets of real vector spaces

In this file we study ample sets in real vector spaces. A set is ample if all its connected
component have full convex hull. Ample sets are an important ingredient for defining ample
differential relations.

## Main results
- `ampleSet_empty` and `ampleSet_univ`: the empty set and `univ` are ample
- `AmpleSet.union`: the union of two ample sets is ample
- `AmpleSet.{pre}image`: being ample is invariant under continuous affine equivalences;
  `AmpleSet.{pre}image_iff` are "iff" versions of these
- `AmpleSet.vadd`: in particular, ample-ness is invariant under affine translations
- `AmpleSet.of_one_lt_codim`: a linear subspace of codimension at least two has an ample complement.
  This is the crucial geometric ingredient which allows to apply convex integration
  to the theory of immersions in positive codimension.

## Implementation notes

A priori, the definition of ample subset asks for a vector space structure and a topology on the
ambient type without any link between those structures. In practice, we care most about using these
for finite-dimensional vector spaces with their natural topology.

All vector spaces in the file are real vector spaces. While the definition generalises to other
connected fields, that is not useful in practice.

## Tags
ample set
-/

/-! ## Definition and invariance -/

open Set

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- A subset of a topological real vector space is ample
if the convex hull of each of its connected components is the full space. -/
def AmpleSet (s : Set F) : Prop :=
  ∀ x ∈ s, convexHull ℝ (connectedComponentIn s x) = univ

/-- A whole vector space is ample. -/
@[simp]
theorem ampleSet_univ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    AmpleSet (univ : Set F) := by
  intro x _
  rw [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ, convexHull_univ]

/-- The empty set in a vector space is ample. -/
@[simp]
theorem ampleSet_empty : AmpleSet (∅ : Set F) := fun _ ↦ False.elim

namespace AmpleSet

/-- The union of two ample sets is ample. -/
theorem union {s t : Set F} (hs : AmpleSet s) (ht : AmpleSet t) : AmpleSet (s ∪ t) := by
  intro x hx
  rcases hx with (h | h) <;>
  -- The connected component of `x ∈ s` in `s ∪ t` contains the connected component of `x` in `s`,
  -- hence is also full; similarly for `t`.
  [have hx := hs x h; have hx := ht x h] <;>
  rw [← Set.univ_subset_iff, ← hx] <;>
  apply convexHull_mono <;>
  apply connectedComponentIn_mono <;>
  [apply subset_union_left; apply subset_union_right]

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- Images of ample sets under continuous affine equivalences are ample. -/
theorem image {s : Set E} (h : AmpleSet s) (L : E ≃ᴬ[ℝ] F) :
    AmpleSet (L '' s) := forall_mem_image.mpr fun x hx ↦
  calc (convexHull ℝ) (connectedComponentIn (L '' s) (L x))
    _ = (convexHull ℝ) (L '' (connectedComponentIn s x)) :=
          .symm <| congrArg _ <| L.toHomeomorph.image_connectedComponentIn hx
    _ = L '' (convexHull ℝ (connectedComponentIn s x)) :=
          .symm <| L.toAffineMap.image_convexHull _
    _ = univ := by rw [h x hx, image_univ, L.surjective.range_eq]

/-- A set is ample iff its image under a continuous affine equivalence is. -/
theorem image_iff {s : Set E} (L : E ≃ᴬ[ℝ] F) :
    AmpleSet (L '' s) ↔ AmpleSet s :=
  ⟨fun h ↦ (L.symm_image_image s) ▸ h.image L.symm, fun h ↦ h.image L⟩

/-- Pre-images of ample sets under continuous affine equivalences are ample. -/
theorem preimage {s : Set F} (h : AmpleSet s) (L : E ≃ᴬ[ℝ] F) : AmpleSet (L ⁻¹' s) := by
  rw [← L.image_symm_eq_preimage]
  exact h.image L.symm

/-- A set is ample iff its pre-image under a continuous affine equivalence is. -/
theorem preimage_iff {s : Set F} (L : E ≃ᴬ[ℝ] F) :
    AmpleSet (L ⁻¹' s) ↔ AmpleSet s :=
  ⟨fun h ↦ L.image_preimage s ▸ h.image L, fun h ↦ h.preimage L⟩

open scoped Pointwise

/-- Affine translations of ample sets are ample. -/
theorem vadd [ContinuousAdd E] {s : Set E} (h : AmpleSet s) {y : E} :
    AmpleSet (y +ᵥ s) :=
  h.image (ContinuousAffineEquiv.constVAdd ℝ E y)

/-- A set is ample iff its affine translation is. -/
theorem vadd_iff [ContinuousAdd E] {s : Set E} {y : E} :
    AmpleSet (y +ᵥ s) ↔ AmpleSet s :=
  AmpleSet.image_iff (ContinuousAffineEquiv.constVAdd ℝ E y)

/-! ## Subspaces of codimension at least two have ample complement -/
section Codimension

/-- Let `E` be a linear subspace in a real vector space.
If `E` has codimension at least two, its complement is ample. -/
theorem of_one_lt_codim [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] {E : Submodule ℝ F}
    (hcodim : 1 < Module.rank ℝ (F ⧸ E)) :
    AmpleSet (Eᶜ : Set F) := fun x hx ↦ by
  rw [E.connectedComponentIn_eq_self_of_one_lt_codim hcodim hx, eq_univ_iff_forall]
  intro y
  by_cases h : y ∈ E
  · obtain ⟨z, hz⟩ : ∃ z, z ∉ E := by
      rw [← not_forall, ← Submodule.eq_top_iff']
      rintro rfl
      simp at hcodim
    refine segment_subset_convexHull ?_ ?_ (mem_segment_sub_add y z) <;>
      simpa [sub_eq_add_neg, Submodule.add_mem_iff_right _ h]
  · exact subset_convexHull ℝ (Eᶜ : Set F) h

end Codimension

end AmpleSet
