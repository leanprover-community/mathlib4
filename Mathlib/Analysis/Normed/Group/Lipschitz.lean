/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz properties of group operations in a normed group
-/

public section

variable {E : Type*} [SeminormedCommGroup E]

/-- Multiplication on a seminormed group `G` as a map `G × G → G` is 2-Lipschitz. -/
@[to_additive /-- Addition on a seminormed group `G` as a map `G × G → G` is `2`-Lipschitz. -/]
lemma lipschitzWith_uncurry_mul : LipschitzWith 2 (fun p : E × E ↦ p.1 * p.2) := by
  refine .of_dist_le_mul fun p q ↦ ?_
  norm_cast
  grw [dist_eq_norm_div, mul_div_mul_comm, norm_mul_le', two_mul, Prod.dist_eq, dist_eq_norm_div,
    dist_eq_norm_div]
  gcongr <;> [exact le_max_left ..; exact le_max_right ..]

@[to_additive]
lemma lipschitzWith_pow (n : ℕ) : LipschitzWith n (fun x : E ↦ x ^ n) :=
  .of_dist_le_mul fun x y ↦ by simpa [dist_eq_norm_div, ← div_pow] using norm_pow_le_mul_norm
