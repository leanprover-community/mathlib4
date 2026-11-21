/-
Copyright (c) 2026 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.StrictConvexSpace

import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Exposed points in strictly convex normed spaces

This file proves that in a real strictly convex normed space, every point of a sphere is an
exposed point of the corresponding closed ball. Furthermore, a point maximizing distance
to a fixed center on any set is exposed. In a nontrivial space, the exposed points of a
closed ball are exactly its sphere.

## Main results

* `StrictConvexSpace.sphere_subset_exposedPoints_closedBall`: every point of a sphere is an exposed
  point of the corresponding closed ball.
* `StrictConvexSpace.mem_exposedPoints_of_isMaxOn_dist`: a point of a set that maximizes distance
  to a fixed center is an exposed point.
* `StrictConvexSpace.exposedPoints_closedBall_eq_sphere`: in a nontrivial space, the exposed points
  of a closed ball are exactly its sphere.
-/

public section

open Set Metric

namespace StrictConvexSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E]

/-- In a real strictly convex normed space, every point of a sphere is an exposed point of the
corresponding closed ball. -/
theorem sphere_subset_exposedPoints_closedBall (z : E) (r : ℝ) :
    sphere z r ⊆ (closedBall z r).exposedPoints ℝ := by
  intro y hy
  obtain ⟨f, hf, hfy⟩ := exists_dual_vector'' ℝ (y - z)
  have bound (v : E) : f v ≤ ‖v‖ :=
    (Real.le_norm_self _).trans ((f.le_of_opNorm_le hf v).trans_eq (one_mul _))
  refine ⟨sphere_subset_closedBall hy, f, fun x hx ↦ ?_⟩
  rw [mem_closedBall_iff_norm] at hx
  rw [mem_sphere_iff_norm] at hy
  have h₁ := bound (x - z)
  simp only [map_sub, RCLike.ofReal_real_eq_id, id_eq] at h₁ hfy
  have hle : f x ≤ f y := by linarith
  refine ⟨hle, fun hge ↦ ?_⟩
  have h₂ := bound (x - z + (y - z))
  simp only [map_sub, map_add] at h₂
  have hxz : ‖x - z‖ = ‖y - z‖ := by linarith
  have hsum : ‖x - z + (y - z)‖ = ‖x - z‖ + ‖y - z‖ := (norm_add_le _ _).antisymm (by linarith)
  exact sub_left_injective (eq_of_norm_eq_of_norm_add_eq hxz hsum)

/-- In a real strictly convex normed space, a point `y ∈ S` that maximizes distance
to a fixed center `z` is an exposed point of `S`. -/
theorem mem_exposedPoints_of_isMaxOn_dist {S : Set E} {z y : E} (hy : y ∈ S)
    (h : IsMaxOn (fun x ↦ dist x z) S y) : y ∈ S.exposedPoints ℝ := by
  obtain ⟨_, f, hf⟩ := sphere_subset_exposedPoints_closedBall z (dist y z) (mem_sphere.mpr rfl)
  exact ⟨hy, f, fun x hx ↦ hf x (mem_closedBall.2 (h hx))⟩

/-- In a nontrivial real strictly convex normed space, the exposed points of a closed ball
are exactly its sphere. -/
theorem exposedPoints_closedBall_eq_sphere [Nontrivial E] {z : E} {r : ℝ} :
    (closedBall z r).exposedPoints ℝ = sphere z r :=
  subset_antisymm
    (exposedPoints_subset_extremePoints.trans extremePoints_closedBall_subset_sphere)
    (sphere_subset_exposedPoints_closedBall z r)

end StrictConvexSpace
