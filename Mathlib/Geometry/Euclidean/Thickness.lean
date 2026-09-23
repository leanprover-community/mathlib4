/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team, Bolton Bailey
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Topology.MetricSpace.AffineThickness

/-!
# Thickness of a set in a Euclidean affine space

In a Euclidean affine space a strict affine subspace admits a unit vector orthogonal to its
direction. Pushing a point along such a vector gives lower bounds for `Metric.ethickness` that
are unavailable in a general metric affine space, and which complement the upper bounds
`Metric.ethickness_cthickening_le` and `Metric.ethickness_closedBall_le`.

## Main results

* `infDist_add_le_of_closedBall_subset_cthickening`: if the closed `ρ`-ball around `x` lies in
  the closed `r`-thickening of a proper affine subspace `A`, then `infDist x A + ρ ≤ r`.
* `Metric.le_ethickness_cthickening`: thickening a nonempty set by `ρ` increases its
  `ethickness` by at least `ρ`, at every rank below the ambient dimension.
* `Metric.le_ethickness_closedBall`: the closed ball of radius `r` has `ethickness` at least `r`
  at every rank below the ambient dimension.
-/

@[expose] public section

open scoped NNReal ENNReal

open Metric EuclideanGeometry

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace E]
  [NormedAddTorsor V E]

/-- If the closed `ρ`-ball around `x` lies in the closed `r`-thickening of an affine subspace `A`
whose direction is not everything, then `infDist x A + ρ ≤ r`: move `x` by `ρ` away from `A`
along a unit vector orthogonal to `A`. -/
lemma infDist_add_le_of_closedBall_subset_cthickening
    {A : AffineSubspace ℝ E} [Nonempty A] [A.direction.HasOrthogonalProjection]
    (hA : A.directionᗮ ≠ ⊥) {x : E} {ρ : ℝ} (hρ : 0 ≤ ρ) {r : ℝ≥0}
    (h : closedBall x ρ ⊆ cthickening r A) : infDist x A + ρ ≤ r := by
  set w : V := x -ᵥ orthogonalProjection A x with hw
  have hwA : w ∈ A.directionᗮ := vsub_orthogonalProjection_mem_direction_orthogonal A x
  obtain ⟨u, huA, hu, hwu⟩ : ∃ u ∈ A.directionᗮ, ‖u‖ = 1 ∧ w = ‖w‖ • u := by
    obtain h0 | h0 := eq_or_ne w 0
    · obtain ⟨v, hvA, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
      exact ⟨‖v‖⁻¹ • v, Submodule.smul_mem _ _ hvA, by simp [norm_smul, hv], by simp [h0]⟩
    · exact ⟨‖w‖⁻¹ • w, Submodule.smul_mem _ _ hwA, by simp [norm_smul, h0], by simp [h0]⟩
  have hy : ρ • u +ᵥ x ∈ closedBall x ρ := by simp [norm_smul, hu, abs_of_nonneg hρ]
  have hp : orthogonalProjection A (ρ • u +ᵥ x) = orthogonalProjection A x := by
    rw [orthogonalProjection_eq_iff_mem, vadd_vsub_assoc]
    exact add_mem (Submodule.smul_mem _ _ huA) hwA
  have := ENNReal.toReal_le_of_le_ofReal r.coe_nonneg (mem_cthickening_iff.1 (h hy))
  rwa [← infDist, ← dist_orthogonalProjection_eq_infDist, hp, dist_eq_norm_vsub V,
    vadd_vsub_assoc, ← hw, hwu, ← add_smul, norm_smul, hu, mul_one,
    Real.norm_of_nonneg (by positivity), add_comm, ← dist_eq_norm_vsub V,
    dist_orthogonalProjection_eq_infDist] at this

namespace Metric

variable [FiniteDimensional ℝ V]

/-- Thickening a nonempty set by `ρ` increases its `ethickness` by at least `ρ`, at every rank
below the ambient dimension. See `Metric.ethickness_cthickening_le` for the reverse inequality. -/
theorem le_ethickness_cthickening {s : Set E} (hs : s.Nonempty) {ρ : ℝ} {n : ℕ}
    (hn : n < Module.finrank ℝ V) :
    ethickness ℝ s n + ENNReal.ofReal ρ ≤ ethickness ℝ (cthickening ρ s) n := by
  obtain hρ | hρ := le_or_gt ρ 0
  · simpa [ENNReal.ofReal_of_nonpos hρ] using ethickness_monotone (self_subset_cthickening s) n
  rw [le_ethickness_iff]
  intro r A hA hsub
  have hperp : A.directionᗮ ≠ ⊥ := by
    grind [Submodule.orthogonal_eq_bot_iff, Submodule.eq_top_iff_finrank_eq (W := A.direction),
      Module.finrank_le_of_rank_le hA]
  obtain ⟨x₀, hx₀⟩ := hs
  have hAne : (A : Set E).Nonempty := by
    by_contra! hAe
    simpa [hAe] using hsub (self_subset_cthickening s hx₀)
  have := hAne.to_subtype
  have hdist (x) (hx : x ∈ s) : infDist x A + ρ ≤ r :=
    infDist_add_le_of_closedBall_subset_cthickening hperp hρ.le
      ((closedBall_subset_cthickening hx ρ).trans hsub)
  have hρr : ρ ≤ r := by grind [hdist x₀ hx₀, infDist_nonneg (x := x₀) (s := (A : Set E))]
  have : ethickness ℝ s n ≤ ENNReal.ofReal (r - ρ) := by
    refine ethickness_le_of_cthickening _ hA fun x hx ↦ mem_cthickening_of_dist_le x
      (orthogonalProjection A x) _ _ (orthogonalProjection_mem x) ?_
    rw [dist_orthogonalProjection_eq_infDist, Real.coe_toNNReal _ (sub_nonneg.2 hρr)]
    grind [hdist x hx]
  grw [this, ← ENNReal.ofReal_add (sub_nonneg.2 hρr) hρ.le, sub_add_cancel,
    ENNReal.ofReal_coe_nnreal]

/-- The closed ball of radius `r` has `ethickness` at least `r`, at every rank below the ambient
dimension. See `Metric.ethickness_closedBall_le` for the reverse inequality. -/
theorem le_ethickness_closedBall {x : E} (r : ℝ≥0) {n : ℕ}
    (hn : n < Module.finrank ℝ V) :
    (r : ℝ≥0∞) ≤ ethickness ℝ (closedBall x r) n := by
  simpa [Set.subsingleton_singleton.ethickness_eq_zero, cthickening_singleton _ r.coe_nonneg]
    using le_ethickness_cthickening (Set.singleton_nonempty x) (ρ := r) hn

end Metric
