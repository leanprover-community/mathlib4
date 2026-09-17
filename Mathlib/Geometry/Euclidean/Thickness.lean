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
    rw [mem_closedBall, dist_eq_norm_vsub V, hydef, vadd_vsub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hρ, hu_norm, mul_one]
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
      _ ≤ |inner ℝ (y -ᵥ a) u| := le_abs_self _
      _ ≤ ‖y -ᵥ a‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ = ‖y -ᵥ a‖ := by rw [hu_norm, mul_one]
      _ = dist y a := (dist_eq_norm_vsub V y a).symm
  linarith [hlb, hy_infDist]

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
  by_cases hρ : ρ ≤ 0
  · rw [ENNReal.ofReal_of_nonpos hρ, add_zero]
    exact ethickness_monotone (Metric.self_subset_cthickening s) n
  · replace hρ : 0 < ρ := not_le.1 hρ
    rw [le_ethickness_iff]
    intro r' A hA hsub
    have hAdim : Module.finrank ℝ A.direction < Module.finrank ℝ V :=
      lt_of_le_of_lt (Module.finrank_le_of_rank_le hA) hn
    have hperp : A.directionᗮ ≠ ⊥ := by
      rw [Ne, Submodule.orthogonal_eq_bot_iff]
      intro htop
      rw [htop, Submodule.topEquiv.finrank_eq] at hAdim
      exact lt_irrefl _ hAdim
    obtain ⟨x₀, hx₀⟩ := hs
    have hAne : (A : Set E).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have hx' := ((closedBall_subset_cthickening hx₀ ρ).trans hsub) (mem_closedBall_self hρ.le)
      rw [h, cthickening_empty] at hx'
      exact hx'
    have : Nonempty A := hAne.to_subtype
    have : A.direction.HasOrthogonalProjection := inferInstance
    -- key per-point bound: for `x ∈ s`, `infDist x A + ρ ≤ r'`.
    have hcov : ∀ x ∈ s, Metric.infDist x (A : Set E) + ρ ≤ (r' : ℝ) := fun x hx =>
      infDist_add_le_of_closedBall_subset_cthickening hAne hperp hρ
        ((closedBall_subset_cthickening hx ρ).trans hsub)
    -- assemble: `s ⊆ cthickening (r' - ρ) A`, so `ethickness s n ≤ r' - ρ`.
    have hρr : ρ ≤ (r' : ℝ) := by
      have := hcov x₀ hx₀
      linarith [Metric.infDist_nonneg (x := x₀) (s := (A : Set E))]
    have hsub' : s ⊆ cthickening ((r' : ℝ) - ρ) (A : Set E) := fun x hx => by
      have hxle : Metric.infDist x (A : Set E) ≤ (r' : ℝ) - ρ := by linarith [hcov x hx]
      rw [Metric.mem_cthickening_iff, ← ENNReal.ofReal_toReal (Metric.infEDist_ne_top hAne)]
      exact ENNReal.ofReal_le_ofReal hxle
    have heth : ethickness ℝ s n ≤ ENNReal.ofReal ((r' : ℝ) - ρ) :=
      ethickness_le_of_cthickening ((r' : ℝ) - ρ).toNNReal hA
        (by rwa [Real.coe_toNNReal _ (by linarith)])
    calc ethickness ℝ s n + ENNReal.ofReal ρ
        ≤ ENNReal.ofReal ((r' : ℝ) - ρ) + ENNReal.ofReal ρ := by gcongr
      _ = ENNReal.ofReal (r' : ℝ) := by
            rw [← ENNReal.ofReal_add (by linarith) hρ.le, sub_add_cancel]
      _ = (r' : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

/-- **Lower bound for the `ethickness` of a closed ball.** At every rank `n` strictly below the
ambient dimension, the closed ball of radius `r` has `ethickness` at least `r`: a ball is the
`r`-thickening of its center, so this is the point-set case of `le_ethickness_cthickening`.
Together with `ethickness_closedBall_le` this pins the value to exactly `r`. -/
theorem le_ethickness_closedBall {x : E} (r : ℝ≥0) {n : ℕ}
    (hn : n < Module.finrank ℝ V) :
    (r : ℝ≥0∞) ≤ ethickness ℝ (closedBall x r) n := by
  have h_nonneg : 0 ≤ (r : ℝ) := r.coe_nonneg
  have h_eq : closedBall x (r : ℝ) = cthickening (r : ℝ) ({x} : Set E) := by
    symm; exact Metric.cthickening_singleton x h_nonneg
  rw [h_eq]
  have h_singleton_nonempty : ({x} : Set E).Nonempty := Set.singleton_nonempty x
  have h_singleton_subsingleton : ({x} : Set E).Subsingleton :=
    Set.subsingleton_singleton (a := x)
  have h_eth_singleton_zero : ethickness ℝ ({x} : Set E) n = 0 :=
    h_singleton_subsingleton.ethickness_eq_zero n
  have h_ineq : ethickness ℝ ({x} : Set E) n + ENNReal.ofReal (r : ℝ) ≤
    ethickness ℝ (cthickening (r : ℝ) ({x} : Set E)) n :=
    le_ethickness_cthickening h_singleton_nonempty hn
  rw [h_eth_singleton_zero, zero_add] at h_ineq
  simpa [ENNReal.ofReal_coe_nnreal] using h_ineq

end Metric
