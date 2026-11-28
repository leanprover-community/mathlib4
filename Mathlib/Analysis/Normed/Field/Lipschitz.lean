/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz properties of inversion and integer powers in a normed division ring
-/

public section

open Metric
open scoped NNReal

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]

/-- The map `x ↦ x⁻¹` in a normed division ring is `A⁻¹ ^ 2`-Lipschitz outside the open ball of
radius `A` around `0` (with `0 < A`). -/
lemma lipschitzOnWith_inv {A : ℝ≥0} (hA : 0 < A) :
    LipschitzOnWith (A⁻¹ ^ 2) (·⁻¹ : 𝕜 → 𝕜) (ball 0 A)ᶜ := by
  simp only [lipschitzOnWith_iff_dist_le_mul, Set.mem_compl_iff, mem_ball_zero_iff, not_lt]
  intro x hx y hy
  simpa [dist_eq_norm] using norm_inv_sub_inv_le hA hx hy

/-- The map `x ↦ x ^ n` in a normed division ring is `|n| * (A ^ (n - 1) ⊔ B ^ (n - 1))`-Lipschitz
on the annulus of radii `A` and `B` around `0` (with `0 < A`). -/
lemma lipschitzOnWith_zpow (n : ℤ) {A B : ℝ≥0} (hA : 0 < A) :
    LipschitzOnWith (n.natAbs * (A ^ (n - 1) ⊔ B ^ (n - 1))) (· ^ n : 𝕜 → 𝕜)
      (closedBall 0 B \ ball 0 A) := by
  simp only [lipschitzOnWith_iff_dist_le_mul, Set.mem_sdiff, mem_closedBall_zero_iff,
    mem_ball_zero_iff, not_lt]
  rintro x ⟨hxB, hAx⟩ y ⟨hyB, hAy⟩
  simpa [dist_eq_norm] using norm_zpow_sub_zpow_le hA hAx hAy hxB hyB n
