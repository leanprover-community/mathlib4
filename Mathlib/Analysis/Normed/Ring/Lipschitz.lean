/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

import Mathlib.Tactic.NoncommRing

/-!
# Lipschitz properties of multiplication and powers in a normed ring
-/

public section

open Metric
open scoped NNReal

variable {R : Type*} [NormedRing R]

/-- Multiplication in a normed ring `R` is `(Bf + Bg)`-Lipschitz on the product of the closed balls
of radii `Bf` and `Bg` around `0`. -/
lemma lipschitzOnWith_uncurry_mul {Bf Bg : ℝ≥0} :
    LipschitzOnWith (Bf + Bg) (fun p : R × R ↦ p.1 * p.2) (closedBall 0 Bf ×ˢ closedBall 0 Bg) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  rintro p ⟨hp₁, hp₂⟩ q ⟨hq₁, hq₂⟩
  rw [mem_closedBall_zero_iff] at hp₁ hp₂ hq₁ hq₂
  simp only [dist_eq_norm, NNReal.coe_add]
  convert_to ‖p.1 * (p.2 - q.2) + (p.1 - q.1) * q.2‖ ≤ Bf * ‖p - q‖ + ‖p - q‖ * Bg
  · noncomm_ring
  · ring
  grw [norm_add_le, norm_mul_le, norm_mul_le, hp₁, hq₂]
  gcongr
  exacts [le_max_right .., le_max_left ..]

/-- The map `x ↦ x ^ n` in a normed ring is `n * B ^ (n - 1)`-Lipschitz on the closed ball of
radius `B` around `0`. -/
lemma lipschitzOnWith_pow (n : ℕ) {B : ℝ≥0} :
    LipschitzOnWith (n * B ^ (n - 1)) (· ^ n : R → R) (closedBall 0 B) := by
  simp only [lipschitzOnWith_iff_dist_le_mul, mem_closedBall_zero_iff]
  intro x hx y hy
  simpa [dist_eq_norm] using norm_pow_sub_pow_le hx hy n
