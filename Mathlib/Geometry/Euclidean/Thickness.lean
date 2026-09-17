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
  the closed `r'`-thickening of an affine subspace `A`, then `infDist x A + ρ ≤ r'`.
* `Metric.le_ethickness_cthickening`: thickening a nonempty set by `ρ` increases its
  `ethickness` by at least `ρ`, at every rank below the ambient dimension.
* `Metric.le_ethickness_closedBall`: the closed ball of radius `r` has `ethickness` at least `r`
  at every rank below the ambient dimension.
-/

@[expose] public section

open scoped NNReal ENNReal

open Metric EuclideanGeometry

section

variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]

/-- Pushing `x` by `ρ` along a unit vector orthogonal to `A.direction` (which exists since
`A` is a strict subspace, `A.directionᗮ ≠ ⊥`) shows that if the closed `ρ`-ball around `x`
lies in the closed `r'`-thickening of `A`, then `infDist x A + ρ ≤ r'`. -/
lemma infDist_add_le_of_closedBall_subset_cthickening
    {A : AffineSubspace ℝ E} [Nonempty A] [A.direction.HasOrthogonalProjection]
    (hAne : (A : Set E).Nonempty) (hperp : A.directionᗮ ≠ ⊥) {x : E} {ρ : ℝ} (hρ : 0 < ρ)
    {r' : ℝ≥0} (hballsub : closedBall x ρ ⊆ cthickening (r' : ℝ) (A : Set E)) :
    Metric.infDist x (A : Set E) + ρ ≤ (r' : ℝ) := by
  set proj : E := (orthogonalProjection A x : E)
  have hres : x -ᵥ proj ∈ A.directionᗮ := vsub_orthogonalProjection_mem_direction_orthogonal A x
  have hd : Metric.infDist x (A : Set E) = ‖x -ᵥ proj‖ := by
    rw [← dist_orthogonalProjection_eq_infDist A x, dist_eq_norm_vsub V]
  -- a unit vector `u ⊥ A.direction` with `⟪x -ᵥ proj, u⟫ = infDist x A`
  obtain ⟨u, hu_mem, hu_norm, hu_inner⟩ :
      ∃ u : V, u ∈ A.directionᗮ ∧ ‖u‖ = 1 ∧
        (inner ℝ (x -ᵥ proj) u) = Metric.infDist x (A : Set E) := by
    rcases eq_or_ne (x -ᵥ proj) 0 with h0 | h0
    · obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.ne_bot_iff _ |>.1 hperp
      refine ⟨‖v‖⁻¹ • v, Submodule.smul_mem _ _ hv_mem, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hv_ne)]
      · rw [h0, inner_zero_left, hd, h0, norm_zero]
    · refine ⟨‖x -ᵥ proj‖⁻¹ • (x -ᵥ proj), Submodule.smul_mem _ _ hres, ?_, ?_⟩
      · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
      · rw [real_inner_smul_right, real_inner_self_eq_norm_mul_norm, hd, ← mul_assoc,
          inv_mul_cancel₀ (norm_ne_zero_iff.2 h0), one_mul]
  -- the pushed point `y = ρ • u +ᵥ x`
  set y : E := (ρ • u) +ᵥ x with hydef
  have hy_ball : y ∈ closedBall x ρ := by
    simp [hydef, dist_eq_norm_vsub V, norm_smul, abs_of_pos hρ, hu_norm]
  have hy_infDist : Metric.infDist y (A : Set E) ≤ (r' : ℝ) :=
    ENNReal.toReal_le_of_le_ofReal (NNReal.coe_nonneg r')
      (Metric.mem_cthickening_iff.1 (hballsub hy_ball))
  have hlb : Metric.infDist x (A : Set E) + ρ ≤ Metric.infDist y (A : Set E) := by
    rw [Metric.le_infDist hAne]
    intro a ha
    have hpa : proj -ᵥ a ∈ A.direction :=
      AffineSubspace.vsub_mem_direction (orthogonalProjection A x).2 ha
    have hinner : (inner ℝ (y -ᵥ a) u) = Metric.infDist x (A : Set E) + ρ := by
      have e1 : y -ᵥ a = ρ • u + (x -ᵥ a) := by rw [hydef, vadd_vsub_assoc]
      have e2 : (x -ᵥ a : V) = (x -ᵥ proj) + (proj -ᵥ a) := (vsub_add_vsub_cancel _ _ _).symm
      rw [e1, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_mul_norm, hu_norm,
        e2, inner_add_left, hu_inner, Submodule.inner_right_of_mem_orthogonal hpa hu_mem]
      ring
    calc Metric.infDist x (A : Set E) + ρ = inner ℝ (y -ᵥ a) u := hinner.symm
      _ ≤ ‖y -ᵥ a‖ * ‖u‖ := real_inner_le_norm _ _
      _ = dist y a := by rw [hu_norm, mul_one, dist_eq_norm_vsub V]
  linarith

end

namespace Metric

variable {V E : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MetricSpace E] [NormedAddTorsor V E]

/-- **Lower bound for the `ethickness` of a thickening.** Thickening a nonempty set by `ρ`
increases its `ethickness` by at least `ρ` at every rank below the ambient dimension: the key
geometric input is that a strict affine subspace admits a unit orthogonal vector, so pushing a
point of `s` by `ρ` along the direction realizing its distance to a covering subspace `A` adds
`ρ` to that distance. Combined with `ethickness_cthickening_le` this gives the equality
`ethickness (cthickening ρ s) n = ethickness s n + ρ`. -/
theorem le_ethickness_cthickening {s : Set E} (hs : s.Nonempty) {ρ : ℝ} {n : ℕ}
    (hn : n < Module.finrank ℝ V) :
    ethickness ℝ s n + ENNReal.ofReal ρ ≤ ethickness ℝ (cthickening ρ s) n := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · simpa [ENNReal.ofReal_of_nonpos hρ] using ethickness_monotone (self_subset_cthickening s) n
  rw [le_ethickness_iff]
  intro r' A hA hsub
  have hperp : A.directionᗮ ≠ ⊥ := by
    intro h
    rw [Submodule.orthogonal_eq_bot_iff] at h
    have := Module.finrank_le_of_rank_le hA
    rw [h, finrank_top] at this
    omega
  obtain ⟨x₀, hx₀⟩ := hs
  have hAne : (A : Set E).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    simpa [h] using hsub (self_subset_cthickening s hx₀)
  have : Nonempty A := hAne.to_subtype
  -- key per-point bound: for `x ∈ s`, `infDist x A + ρ ≤ r'`.
  have hcov (x) (hx : x ∈ s) : infDist x (A : Set E) + ρ ≤ r' :=
    infDist_add_le_of_closedBall_subset_cthickening hAne hperp hρ
      ((closedBall_subset_cthickening hx ρ).trans hsub)
  -- assemble: `s ⊆ cthickening (r' - ρ) A`, so `ethickness s n ≤ r' - ρ`.
  have hρr : ρ ≤ r' := by linarith [hcov x₀ hx₀, infDist_nonneg (x := x₀) (s := (A : Set E))]
  have heth : ethickness ℝ s n ≤ ENNReal.ofReal (r' - ρ) := by
    refine ethickness_le_of_cthickening _ hA fun x hx ↦ ?_
    rw [Real.coe_toNNReal _ (by linarith), mem_cthickening_iff,
      ← ENNReal.ofReal_toReal (infEDist_ne_top hAne)]
    have : infDist x (A : Set E) ≤ r' - ρ := by linarith [hcov x hx]
    exact ENNReal.ofReal_le_ofReal this
  grw [heth, ← ENNReal.ofReal_add (by linarith) hρ.le, sub_add_cancel, ENNReal.ofReal_coe_nnreal]

/-- **Lower bound for the `ethickness` of a closed ball.** At every rank `n` strictly below the
ambient dimension, the closed ball of radius `r` has `ethickness` at least `r`: a ball is the
`r`-thickening of its center, so this is the point-set case of `le_ethickness_cthickening`.
Together with `ethickness_closedBall_le` this pins the value to exactly `r`. -/
theorem le_ethickness_closedBall {x : E} (r : ℝ≥0) {n : ℕ}
    (hn : n < Module.finrank ℝ V) :
    (r : ℝ≥0∞) ≤ ethickness ℝ (closedBall x r) n := by
  simpa [Set.subsingleton_singleton.ethickness_eq_zero, cthickening_singleton _ r.coe_nonneg]
    using le_ethickness_cthickening (Set.singleton_nonempty x) (ρ := r) hn

end Metric
