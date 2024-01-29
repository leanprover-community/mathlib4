/-
Copyright (c) 2024 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import Mathlib.Topology.ContinuousFunction.ZeroAtInfty

/-!
# ZeroAtInftyContinuousMapClass in normed additive groups

In this file we give a characterization of the predicate `zero_at_infty` from
`ZeroAtInftyContinuousMapClass`. A continuous map `f` is zero at infinity if and only if
for every `ε > 0` there exists a `r : ℝ` such that for all `x : E` with `r < ‖x‖` it holds that
`‖f x‖ < ε`.
-/

open Topology Filter

variable {E F 𝓕 : Type*}
variable [SeminormedAddGroup E] [SeminormedAddCommGroup F] [ZeroAtInftyContinuousMapClass 𝓕 E F]

theorem ZeroAtInftyContinuousMapClass.norm_le (f : 𝓕) (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℝ), ∀ (x : E) (_hx : r < ‖x‖), ‖f x‖ < ε := by
  have h := zero_at_infty f
  rw [tendsto_zero_iff_norm_tendsto_zero, tendsto_def] at h
  specialize h (Metric.ball 0 ε) (Metric.ball_mem_nhds 0 hε)
  rw [mem_cocompact] at h
  rcases h with ⟨s, hsc, hs⟩
  have := hsc.isBounded
  rw [Metric.isBounded_iff_subset_closedBall 0] at this
  rcases this with ⟨r, hr⟩
  use r
  intro x hr'
  rw [← Set.compl_subset_compl] at hr
  have : x ∈ (fun x ↦ ‖f x‖) ⁻¹' Metric.ball 0 ε := by
    apply hs
    apply hr
    simp [hr']
  simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, norm_norm] at this
  exact this

variable [ProperSpace E]

theorem zero_at_infty_of_norm_le (f : E → F)
    (h : ∀ (ε : ℝ) (_hε : 0 < ε), ∃ (r : ℝ), ∀ (x : E) (_hx : r < ‖x‖), ‖f x‖ < ε) :
    Tendsto f (cocompact E) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  intro s hs
  simp only [mem_map, mem_cocompact]
  rw [Metric.mem_nhds_iff] at hs
  rcases hs with ⟨ε, hε, hs⟩
  rcases h ε hε with ⟨r, hr⟩
  use Metric.closedBall 0 r
  refine ⟨isCompact_closedBall _ _, ?_⟩
  intro x hx
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le,
    Set.mem_preimage] at hx ⊢
  apply hs
  simp only [Metric.mem_ball, dist_zero_right, norm_norm, hr x hx]
