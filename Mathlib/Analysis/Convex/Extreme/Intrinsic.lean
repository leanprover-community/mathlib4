/-
Copyright (c) 2026 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Intrinsic

/-!
# Extreme subsets and intrinsic interiors

This file relates the extreme subsets of a set `K` to intrinsic interiors. A convex extreme subset
of `K` is called a *face* of `K`.

## Main results

* `IsExtreme.subset_of_mem_intrinsicInterior`: An extreme subset of `K` containing a point of the
  intrinsic interior of `S ⊆ K` contains `S`.
* `IsExtreme.subset_intrinsicFrontier`: A proper extreme subset of `K` lies in the intrinsic
  frontier of `K`.
* `IsExtreme.convex_of_intrinsicInterior_nonempty`: An extreme subset of a convex set with nonempty
  intrinsic interior is convex.
* `Convex.existsUnique_isExtreme_mem_intrinsicInterior`: In finite dimensions, every point of a
  convex set `K` lies in the intrinsic interior of a unique extreme subset of `K`.
* `IsExtreme.inter_affineSpan_eq`: In finite dimensions, a face `F` of `K` is equal to
  `K ∩ affineSpan ℝ F`.

## References

* Sections 6 and 18 of [R. T. Rockafellar, *Convex Analysis*][rockafellar1970]
-/

public section

open Set AffineSubspace

section Topological

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul 𝕜 E] {K F G S : Set E} {p : E}

/-- If an extreme subset `F` of `K` contains an intrinsic-interior point of `S ⊆ K`, then it
contains every point of `K` lying in the affine span of `S`. -/
theorem IsExtreme.inter_affineSpan_subset_of_mem_intrinsicInterior (hF : IsExtreme 𝕜 K F)
    (hSK : S ⊆ K) (hpF : p ∈ F) (hpiS : p ∈ intrinsicInterior 𝕜 S) :
    K ∩ affineSpan 𝕜 S ⊆ F := fun _ ⟨hyK, hyS⟩ ↦
  let ⟨_, ht, hz⟩ := exists_pos_add_smul_sub_mem_of_mem_intrinsicInterior hpiS hyS
  hF.mem_of_add_smul_sub_mem hyK hpF ht (hSK hz)

/-- If an extreme subset `F` of `K` contains an intrinsic-interior point of a subset `S` of `K`,
then `S ⊆ F`. In particular, an extreme subset `S` of `K` is the least extreme subset of `K`
containing any given point of its intrinsic interior. -/
theorem IsExtreme.subset_of_mem_intrinsicInterior (hF : IsExtreme 𝕜 K F) (hSK : S ⊆ K)
    (hpF : p ∈ F) (hpiS : p ∈ intrinsicInterior 𝕜 S) : S ⊆ F :=
  fun _ hy ↦ hF.inter_affineSpan_subset_of_mem_intrinsicInterior hSK hpF hpiS
    ⟨hSK hy, subset_affineSpan 𝕜 S hy⟩

/-- If an extreme subset `F` of `K` contains an intrinsic-interior point of `K`, then `F = K`.
For the topological interior, combine with `interior_subset_intrinsicInterior`. -/
theorem IsExtreme.eq_of_mem_intrinsicInterior (hF : IsExtreme 𝕜 K F) (hpF : p ∈ F)
    (hpiK : p ∈ intrinsicInterior 𝕜 K) : F = K :=
  hF.subset.antisymm (hF.subset_of_mem_intrinsicInterior subset_rfl hpF hpiK)

/-- Two extreme subsets of `K` whose intrinsic interiors meet are equal. -/
theorem IsExtreme.eq_of_mem_intrinsicInterior_of_mem_intrinsicInterior (hF : IsExtreme 𝕜 K F)
    (hG : IsExtreme 𝕜 K G) (hpiF : p ∈ intrinsicInterior 𝕜 F)
    (hpiG : p ∈ intrinsicInterior 𝕜 G) : F = G :=
  (hG.subset_of_mem_intrinsicInterior hF.subset (intrinsicInterior_subset hpiG) hpiF).antisymm
    (hF.subset_of_mem_intrinsicInterior hG.subset (intrinsicInterior_subset hpiF) hpiG)

/-- An extreme subset `F` of a convex set `K` is convex if its intrinsic interior is nonempty. -/
theorem IsExtreme.convex_of_intrinsicInterior_nonempty (hF : IsExtreme 𝕜 K F) (hK : Convex 𝕜 K)
    (hiF : (intrinsicInterior 𝕜 F).Nonempty) : Convex 𝕜 F := by
  obtain ⟨p, hpiF⟩ := hiF
  have hpF := intrinsicInterior_subset hpiF
  have hFeq : F = {y ∈ K | ∃ t : 𝕜, 0 < t ∧ p + t • (p - y) ∈ K} :=
    IsLeast.unique (s := {G | IsExtreme 𝕜 K G ∧ p ∈ G}) ⟨⟨hF, hpF⟩, fun _ ⟨hG, hpG⟩ ↦
      hG.subset_of_mem_intrinsicInterior hF.subset hpG hpiF⟩
      (hK.isLeast_isExtreme_setOfPred_add_smul_sub_mem (hF.subset hpF))
  exact hFeq ▸ hK.convex_setOfPred_add_smul_sub_mem (hF.subset hpF)

/-- A proper extreme subset `F` of `K` lies in the intrinsic frontier of `K`. -/
theorem IsExtreme.subset_intrinsicFrontier (hF : IsExtreme 𝕜 K F) (hFK : F ≠ K) :
    F ⊆ intrinsicFrontier 𝕜 K := by
  rw [← intrinsicClosure_sdiff_intrinsicInterior]
  exact fun y hy ↦ ⟨subset_intrinsicClosure (hF.subset hy),
    fun hi ↦ hFK (hF.eq_of_mem_intrinsicInterior hy hi)⟩

end Topological

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K F : Set E} {p : E}

/-- In finite dimensions, a face `F` of `K` is equal to the intersection of `K` with the
affine span of `F`. -/
theorem IsExtreme.inter_affineSpan_eq (hF : IsExtreme ℝ K F) (hFc : Convex ℝ F) :
    K ∩ affineSpan ℝ F = F := by
  obtain rfl | hFne := F.eq_empty_or_nonempty
  · simp
  obtain ⟨p, hpiF⟩ := hFne.intrinsicInterior hFc
  exact (hF.inter_affineSpan_subset_of_mem_intrinsicInterior hF.subset
    (intrinsicInterior_subset hpiF) hpiF).antisymm
      (subset_inter hF.subset (subset_affineSpan ℝ F))

/-- In finite dimensions, the affine span of a proper face `F` of `K` is strictly smaller
than the affine span of `K`. -/
theorem IsExtreme.affineSpan_lt (hF : IsExtreme ℝ K F) (hFc : Convex ℝ F) (hFK : F ≠ K) :
    affineSpan ℝ F < affineSpan ℝ K :=
  (affineSpan_mono ℝ hF.subset).lt_of_ne fun h ↦ hFK <| by
    rw [← hF.inter_affineSpan_eq hFc, h, inter_eq_left.mpr (subset_affineSpan ℝ K)]

/-- In finite dimensions, the vector span of a nonempty proper face `F` of `K` has strictly
smaller dimension than the vector span of `K`.

Nonemptiness is needed: the empty face of a point has the same dimension. -/
theorem IsExtreme.finrank_vectorSpan_lt (hF : IsExtreme ℝ K F) (hFc : Convex ℝ F)
    (hFne : F.Nonempty) (hFK : F ≠ K) :
    Module.finrank ℝ (vectorSpan ℝ F) < Module.finrank ℝ (vectorSpan ℝ K) := by
  rw [← direction_affineSpan, ← direction_affineSpan]
  exact Submodule.finrank_lt_finrank_of_lt <| direction_lt_of_nonempty
    (hF.affineSpan_lt hFc hFK) ((affineSpan_nonempty ℝ).mpr hFne)

/-- In finite dimensions, a face of a closed set is closed. -/
protected theorem IsExtreme.isClosed (hF : IsExtreme ℝ K F) (hFc : Convex ℝ F)
    (hK : IsClosed K) : IsClosed F := by
  rw [← hF.inter_affineSpan_eq hFc]
  exact hK.inter (affineSpan ℝ F).isClosed_of_finiteDimensional

/-- In finite dimensions, every point `p` of a convex set `K` lies in the intrinsic interior of
some face `F`. -/
theorem Convex.exists_isExtreme_mem_intrinsicInterior (hK : Convex ℝ K) (hpK : p ∈ K) :
    ∃ F : Set E, Convex ℝ F ∧ IsExtreme ℝ K F ∧ p ∈ intrinsicInterior ℝ F := by
  have hF := hK.convex_setOfPred_add_smul_sub_mem hpK
  refine ⟨_, hF, (hK.isLeast_isExtreme_setOfPred_add_smul_sub_mem hpK).1.1,
    hF.mem_intrinsicInterior_iff.mpr ⟨⟨hpK, 1, one_pos, by simpa⟩,
      fun y ⟨hy, t, ht, hz⟩ ↦ ⟨t, ht, hz, t⁻¹, inv_pos.mpr ht, ?_⟩⟩⟩
  -- The segment from `z = p + t • (p - y)` through `p` extends beyond `p` to `y`.
  simpa [smul_smul, ht.ne'] using hy

/-- In finite dimensions, every point `p` of a convex set `K` lies in the intrinsic interior of a
unique extreme subset `F`. This subset is a face by
`IsExtreme.convex_of_intrinsicInterior_nonempty`. -/
theorem Convex.existsUnique_isExtreme_mem_intrinsicInterior (hK : Convex ℝ K) (hpK : p ∈ K) :
    ∃! F : Set E, IsExtreme ℝ K F ∧ p ∈ intrinsicInterior ℝ F := by
  obtain ⟨F, -, hF⟩ := hK.exists_isExtreme_mem_intrinsicInterior hpK
  exact .intro F hF fun G hG ↦
    hG.1.eq_of_mem_intrinsicInterior_of_mem_intrinsicInterior hF.1 hG.2 hF.2

end FiniteDimensional
