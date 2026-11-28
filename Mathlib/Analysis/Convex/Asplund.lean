/-
Copyright (c) 2026 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Extreme.Intrinsic
public import Mathlib.LinearAlgebra.AffineSpace.Dimension

import Mathlib.Analysis.Convex.Straszewicz

/-!
# Asplund's theorem

Asplund's theorem: every `k`-extreme point of a closed convex set `K` in a
finite-dimensional Hausdorff real topological vector space is a limit of `k`-exposed points.
A point is `k`-extreme if it belongs to a face of `K` of affine dimension at most `k`, and
`k`-exposed if it belongs to an exposed face of `K` of affine dimension at most `k`. For `k = 0`,
this is Straszewicz's theorem.

The theorem is proved in the following form: every extreme subset `F` of `K` lies in the closure
of the union of the exposed subsets of `K` of the same or smaller affine dimension. The affine
dimension of a set `s` is `(affineSpan ℝ s).finDim`.

## Main results

* `IsExtreme.subset_closure_sUnion_isExposed_finDim_le`: **Asplund's theorem**.
* `IsExtreme.isExposed_of_mem_exposedPoints_inter`: An extreme subset `F` of a convex set `K` is
  exposed if a point of its intrinsic interior is an exposed point of `K ∩ M`, where `M` is an
  affine subspace whose direction is a topological complement of `vectorSpan 𝕜 F`.

## References

* [Edgar Asplund, *A `k`-extreme point is the limit of `k`-exposed points*][asplund1963]
-/

public section

open Set AffineSubspace Module Submodule

section TopologicalVectorSpace

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E]

/-- Let `F` be an extreme subset of a convex set `K`, and let `M` be an affine subspace whose
direction is a topological complement of `vectorSpan 𝕜 F`. If a point `p` in the intrinsic
interior of `F` is exposed in `K ∩ M`, then `F` is exposed in `K`. -/
theorem IsExtreme.isExposed_of_mem_exposedPoints_inter {K F : Set E} {M : AffineSubspace 𝕜 E}
    {p : E} (hF : IsExtreme 𝕜 K F) (hK : Convex 𝕜 K)
    (hFM : IsTopCompl (vectorSpan 𝕜 F) M.direction) (hpiF : p ∈ intrinsicInterior 𝕜 F)
    (hpe : p ∈ (K ∩ M).exposedPoints 𝕜) : IsExposed 𝕜 K F := by
  obtain ⟨⟨hpK, hpM⟩, f, hf⟩ := hpe
  have hpF := intrinsicInterior_subset hpiF
  let π := M.direction.projectionL (vectorSpan 𝕜 F) hFM.symm
  let g : StrongDual 𝕜 E := f ∘L π
  have hg (y : E) : g y - g p = f (π (y - p)) := (map_sub g y p).symm
  have key (y : E) (hy : y ∈ K) : g y ≤ g p ∧ (g p ≤ g y → y ∈ F) := by
    rw [← sub_nonpos (a := g y), ← sub_nonneg (b := g p), hg]
    set w := π (y - p)
    have hu : y - p - w ∈ vectorSpan 𝕜 F := sub_projection_mem hFM.isCompl.symm _
    obtain ⟨s, hs, hsF⟩ :=
      (eventually_add_smul_mem_of_mem_intrinsicInterior hpiF (neg_mem hu)).exists_gt
    set z := p + (s / (s + 1)) • w
    have hseg : z ∈ openSegment 𝕜 y (p + s • -(y - p - w)) := (mem_openSegment_translate 𝕜 (-p)).mp
      (mem_openSegment_iff_div.mpr ⟨s, 1, hs, one_pos, by module⟩)
    have hz : z ∈ K ∩ M := ⟨hK.openSegment_subset hy (hF.subset hsF) hseg,
      (vsub_right_mem_direction_iff_mem hpM z).mp (by
        rw [vsub_eq_sub, add_sub_cancel_left]
        exact M.direction.smul_mem _ (projectionL_apply_mem hFM.symm _))⟩
    have hfz : f z - f p = s / (s + 1) * f w := by simp [z]
    have hpos : 0 < s / (s + 1) := by positivity
    refine ⟨nonpos_of_mul_nonpos_right (hfz ▸ sub_nonpos.mpr (hf z hz).1) hpos, fun hw ↦ ?_⟩
    have hzp : z = p := (hf z hz).2 (sub_nonneg.mp (hfz ▸ mul_nonneg hpos.le hw))
    exact hF.left_mem_of_mem_openSegment hy (hF.subset hsF) hpF (hzp ▸ hseg)
  have hgF (y : E) (hy : y ∈ F) : g y = g p := by
    have hπ : π (y - p) = 0 :=
      projectionL_apply_eq_zero_of_mem_right hFM.symm (vsub_mem_vectorSpan 𝕜 hy hpF)
    rw [← sub_eq_zero, hg, hπ, map_zero]
  refine fun _ ↦ ⟨g, Subset.antisymm (fun y hy ↦ ⟨hF.subset hy, fun z hz ↦ ?_⟩) fun y hy ↦ ?_⟩
  · exact hgF y hy ▸ (key z hz).1
  · exact (key y hy.1).2 (hy.2 p hpK)

end TopologicalVectorSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]

/-- **Asplund's theorem**: in a finite-dimensional Hausdorff real topological vector space, every
extreme subset `F` of a closed convex set `K` lies in the closure of the union of the exposed
faces of `K` of the same or smaller affine dimension. -/
theorem IsExtreme.subset_closure_sUnion_isExposed_finDim_le {K F : Set E}
    (hF : IsExtreme ℝ K F) (hK : IsClosed K) (hc : Convex ℝ K) :
    F ⊆ closure (⋃₀ {G | IsExposed ℝ K G ∧
      (affineSpan ℝ G).finDim ≤ (affineSpan ℝ F).finDim}) := by
  refine fun x hx ↦ mem_closure_iff.mpr fun U hU hxU ↦ ?_
  -- Let `F₀` be an extreme subset of least dimension meeting `U`, and `x₀ ∈ F₀ ∩ U`.
  obtain ⟨F₀, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun G ↦ IsExtreme ℝ K G ∧ (G ∩ U).Nonempty) (fun G ↦ finrank ℝ (vectorSpan ℝ G))
    ⟨F, hF, x, hx, hxU⟩
  obtain ⟨hF₀, x₀, hx₀, hx₀U⟩ := hmin.prop
  -- Cut `K` by an affine subspace `M ∋ x₀` complementary to `F₀`.
  obtain ⟨W, hW⟩ := (vectorSpan ℝ F₀).exists_isCompl
  obtain ⟨M, hx₀M, rfl⟩ : ∃ M : AffineSubspace ℝ E, x₀ ∈ M ∧ M.direction = W :=
    ⟨mk' x₀ W, self_mem_mk' x₀ W, direction_mk' x₀ W⟩
  -- By Straszewicz's theorem, some exposed point `q` of `K ∩ M` lies in `U`.
  obtain ⟨q, hqU, hq⟩ := mem_closure_iff.mp
    (IsClosed.extremePoints_subset_closure_exposedPoints
      (hK.inter (M.isClosed_direction_iff.mp M.direction.isClosed_of_finiteDimensional))
      (hc.inter M.convex) (hF₀.mem_extremePoints_inter_of_disjoint hx₀ hx₀M hW.disjoint)) U hU hx₀U
  -- The face `G`, with `q` in its intrinsic interior, has the same dimension as `F₀`.
  obtain ⟨G, -, hG, hqG⟩ := hc.exists_isExtreme_mem_intrinsicInterior hq.1.1
  have hdisj := disjoint_vectorSpan_direction_of_mem_extremePoints_inter hG.subset hqG
    (exposedPoints_subset_extremePoints hq)
  have hcompl_dim := Submodule.finrank_add_eq_of_isCompl hW
  have hG_dim_le : finrank ℝ (vectorSpan ℝ G) ≤ finrank ℝ (vectorSpan ℝ F₀) := by
    have hsum_le := Submodule.finrank_add_finrank_le_of_disjoint hdisj
    omega
  have hmin_dim_le : finrank ℝ (vectorSpan ℝ F₀) ≤ finrank ℝ (vectorSpan ℝ G) :=
    hmin.le ⟨hG, q, intrinsicInterior_subset hqG, hqU⟩
  have hG_dim : finrank ℝ (vectorSpan ℝ G) = finrank ℝ (vectorSpan ℝ F₀) :=
    hG_dim_le.antisymm hmin_dim_le
  have hF₀_dim_le : finrank ℝ (vectorSpan ℝ F₀) ≤ finrank ℝ (vectorSpan ℝ F) :=
    hmin.le ⟨hF, x, hx, hxU⟩
  have hGM : IsCompl (vectorSpan ℝ G) M.direction :=
    (Submodule.isCompl_iff_disjoint _ _ (by rw [hG_dim]; exact hcompl_dim.ge)).mpr hdisj
  have hGM' : IsTopCompl (vectorSpan ℝ G) M.direction :=
    hGM.isTopCompl_of_isClosed_of_finiteDimensional (vectorSpan ℝ G).isClosed_of_finiteDimensional
  have hqG' := intrinsicInterior_subset hqG
  refine ⟨q, hqU, G, ⟨hG.isExposed_of_mem_exposedPoints_inter hc hGM' hqG hq, ?_⟩, hqG'⟩
  have hdim {s : Set E} (hs : s.Nonempty) :
      (affineSpan ℝ s).finDim = finrank ℝ (vectorSpan ℝ s) := by
    rw [finDim_eq_finrank (mt (affineSpan_eq_bot ℝ).mp hs.ne_empty), direction_affineSpan]
  rw [hdim ⟨q, hqG'⟩, hdim ⟨x, hx⟩]
  exact_mod_cast hG_dim.trans_le hF₀_dim_le
