/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Further lemmas about normed groups

This file contains further lemmas about normed groups, requiring heavier imports than
`Mathlib/Analysis/Normed/Group/Basic.lean`.

## TODO

- Move lemmas from `Basic` to other places, including this file.

-/

public section

variable {E : Type*} [SeminormedAddCommGroup E]
open NNReal

open scoped Topology

theorem eventually_nnnorm_sub_lt (x₀ : E) {ε : ℝ≥0} (ε_pos : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ‖x - x₀‖₊ < ε :=
  (continuousAt_id.sub continuousAt_const).nnnorm (gt_mem_nhds <| by simpa)

theorem eventually_norm_sub_lt (x₀ : E) {ε : ℝ} (ε_pos : 0 < ε) :
    ∀ᶠ x in 𝓝 x₀, ‖x - x₀‖ < ε :=
  (continuousAt_id.sub continuousAt_const).norm (gt_mem_nhds <| by simpa)

section Dense

open Metric

/-- Let `G` be a seminormed group. If a subgroup `H` is `ε`-dense for
some `ε < 1`, that is `infDist g H ≤ ε * ‖g‖` for every `g : G`, then `H` is
dense. This is [BGR, Prop 1.1.4./2][bosch-guntzer-remmert]. -/
@[to_additive]
lemma Subgroup.dense_of_infDist_le {G : Type*} [SeminormedGroup G]
    (H : Subgroup G) (ε : ℝ) (h1 : 0 < ε) (h2 : ε < 1)
    (h : ∀ g : G, infDist g H ≤ ε * ‖g‖) : Dense (H : Set G) := by
  simp only [dense_iff_closure_eq, Set.eq_univ_iff_forall, OneMemClass.coe_nonempty,
    mem_closure_iff_infDist_zero]
  intro g
  by_contra hg
  obtain ⟨y, hy, _⟩ : ∃ y ∈ H, dist g y < ε⁻¹ * infDist g H :=
    (infDist_lt_iff ⟨1, H.one_mem⟩).mp ((lt_mul_iff_one_lt_left (lt_of_le_of_ne infDist_nonneg
      (Ne.symm hg))).mpr ((one_lt_inv₀ h1).mpr h2))
  obtain ⟨z, hz, _⟩ : ∃ z ∈ H, dist (y⁻¹ * g) z < infDist g H := by
    refine (infDist_lt_iff ⟨1, H.one_mem⟩).mp (lt_of_le_of_lt (h (y⁻¹ * g)) ?_)
    calc ε * ‖y⁻¹ * g‖
      _ = ε * dist g y := by rw [dist_eq_norm_inv_mul']
      _ < ε * (ε⁻¹ * infDist g H) := by gcongr
      _ = infDist g (H : Set G) := by rw [← mul_assoc, mul_inv_cancel₀ h1.ne', one_mul]
  have : dist g (y * z) < infDist g (H : Set G) := by
    rwa [dist_eq_norm_inv_mul, ← mul_assoc, ← inv_inv (g⁻¹ * y),
      ← SeminormedGroup.dist_eq (g⁻¹ * y)⁻¹ z, mul_inv_rev, inv_inv]
  exact absurd this (not_lt.mpr (infDist_le_dist_of_mem (mul_mem hy hz)))

end Dense
