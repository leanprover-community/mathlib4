/-
Copyright (c) 2026 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Order.Filter.Extr
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Affine diameters of compact convex sets

An *affine diameter* of a compact convex set `K` with nonempty interior is a segment `[x, y]` with
`x, y ∈ K` such that `K` has two distinct parallel supporting hyperplanes, one through `x` and one
through `y`. We state this using a nonzero continuous linear functional `f` that attains its
maximum on `K` at `x` and its minimum on `K` at `y`. The hyperplanes are then the level sets
`{w | f w = f x}` and `{w | f w = f y}`. They are parallel because they are level sets of the same
functional, they support `K` because `f x` and `f y` are the extreme values of `f` on `K`, and
they are distinct because `f` is not constant on a set with nonempty interior.

## Main results

* `IsCompact.exists_mem_segment_isMaxOn_isMinOn`: every point of a compact convex set with
  nonempty interior in a nontrivial Hausdorff real topological vector space lies on an affine
  diameter.

## References

* [V. Soltan, *Affine diameters of convex bodies—a survey*][soltan2005]
-/

public section

open scoped Topology

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [Nontrivial E]

/-- Every point `z` of a compact convex set `K` with nonempty interior in a nontrivial Hausdorff
real topological vector space lies on an affine diameter of `K`: a segment `[x, y]` with
`x, y ∈ K` such that some nonzero continuous linear functional attains its maximum on `K` at `x`
and its minimum on `K` at `y`. -/
theorem IsCompact.exists_mem_segment_isMaxOn_isMinOn {K : Set E} (hK : IsCompact K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) {z : E} (hz : z ∈ K) :
    ∃ x ∈ K, ∃ y ∈ K, z ∈ segment ℝ x y ∧
      ∃ f : StrongDual ℝ E, f ≠ 0 ∧ IsMaxOn f K x ∧ IsMinOn f K y := by
  by_cases hzi : z ∈ interior K; swap
  · -- A functional supporting `K` at `z` attains its maximum on `K` at `z`.
    obtain ⟨f, hf, hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point hc hzi hi
    obtain ⟨y, hy, hmin⟩ := hK.exists_isMinOn ⟨z, hz⟩ f.continuous.continuousOn
    exact ⟨z, hz, y, hy, left_mem_segment ℝ z y, f, hf, isMaxOn_iff.mpr hmax, hmin⟩
  -- Let `s` be the translate of `K` that moves `z` to the origin.
  have hKz : K ∈ 𝓝 z := mem_interior_iff_mem_nhds.mp hzi
  let s : Set E := (z + ·) ⁻¹' K
  have hs : Convex ℝ s := hc.translate_preimage_right z
  have hsc : IsCompact s := (Homeomorph.addLeft z).isCompact_preimage.mpr hK
  have hs₀ : s ∈ 𝓝 0 := (continuous_const_add z).continuousAt.preimage_mem_nhds (by rwa [add_zero])
  -- Choose `y ∈ K` maximizing `gauge s (z - y)`. The maximum `m` is positive.
  obtain ⟨y, hy, hymax⟩ := hK.exists_isMaxOn (f := fun w ↦ gauge s (z - w)) ⟨z, hz⟩
    ((continuous_gauge hs hs₀).comp (continuous_sub_left z)).continuousOn
  set m := gauge s (z - y)
  have hle {w : E} (hw : w ∈ K) : gauge s (z - w) ≤ m := isMaxOn_iff.mp hymax w hw
  have hm : 0 < m := by
    obtain ⟨w, hw, hwz⟩ := (infinite_of_mem_nhds z hKz).nontrivial.exists_ne z
    exact ((gauge_pos (absorbent_nhds_zero hs₀) (hsc.isVonNBounded ℝ)).mpr
      (sub_ne_zero.mpr hwz.symm)).trans_le (hle hw)
  have hg (w : E) : gauge s (m⁻¹ • (z - w)) = m⁻¹ * gauge s (z - w) :=
    gauge_smul_of_nonneg (inv_nonneg.mpr hm.le) _
  -- The map `w ↦ z + m⁻¹ • (z - w)` sends `K` into `K` and sends `y` outside the interior of `K`.
  have hmem {w : E} (hw : w ∈ K) : z + m⁻¹ • (z - w) ∈ K :=
    hsc.isClosed.closure_subset <| (gauge_le_one_iff_mem_closure hs hs₀).mp <|
      (hg w).trans_le <| (inv_mul_le_one₀ hm).mpr (hle hw)
  have hx : z + m⁻¹ • (z - y) ∉ interior K := fun h ↦
    ((gauge_lt_one_iff_mem_interior hs hs₀).mpr
      (preimage_interior_subset_interior_preimage (continuous_const_add z) h)).ne
      (by rw [hg, inv_mul_cancel₀ hm.ne'])
  -- A functional supporting `K` at `z + m⁻¹ • (z - y)` attains its minimum on `K` at `y`.
  obtain ⟨f, hf, hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point hc hx hi
  refine ⟨_, hmem hy, y, hy, ?_, f, hf, isMaxOn_iff.mpr hmax, isMinOn_iff.mpr fun w hw ↦ ?_⟩
  · rw [mem_segment_iff_sameRay, sub_add_cancel_left, ← smul_neg, neg_sub]
    exact SameRay.sameRay_pos_smul_left _ (inv_pos.mpr hm)
  · simpa only [map_add, map_smul, map_sub, smul_eq_mul, add_le_add_iff_left, sub_le_sub_iff_left,
      mul_le_mul_iff_right₀ (inv_pos.mpr hm)] using hmax _ (hmem hw)
