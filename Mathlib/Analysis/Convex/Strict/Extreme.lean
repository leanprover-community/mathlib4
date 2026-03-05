/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.StrictConvexSpace

/-! # Extreme points in strictly convex spaces

This file collects some results of extreme points of sets in strictly convex spaces.
In particular, we show that in a nontrivial strictly convex space,
the sphere is contained in the extreme points of the closed ball. -/

public section

open Set Metric

lemma StrictConvex.mem_extremePoints_of_mem_sdiff_interior {𝕜 A : Type*} [Semiring 𝕜]
    [PartialOrder 𝕜] [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] {C : Set A}
    (hc : StrictConvex 𝕜 C) {x : A} (hx : x ∈ C \ interior C) : x ∈ extremePoints 𝕜 C := by
  refine ⟨hx.1, fun y hy z hz ⟨a, b, ha, hb, hab, hxab⟩ ↦ ?_⟩
  have hyz : y = z := by
    by_contra
    exact hx.2 <| hxab ▸ hc hy hz this ha hb hab
  rwa [← hyz, ← add_smul, hab, one_smul] at hxab

section Normed
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

lemma StrictConvexSpace.sphere_subset_extremePoints_closedBall [StrictConvexSpace ℝ A]
    (a : A) {r : ℝ} (hr : r ≠ 0) : sphere a r ⊆ extremePoints ℝ (closedBall a r) := fun _ hx ↦ by
  rw [← frontier_closedBall _ hr, frontier, closure_closedBall] at hx
  exact (_root_.strictConvex_closedBall ℝ _ _).mem_extremePoints_of_mem_sdiff_interior hx

lemma StrictConvexSpace.sphere_subset_extremePoints_closedBall' [Nontrivial A] {a : A} {r : ℝ}
    [StrictConvexSpace ℝ A] : sphere a r ⊆ extremePoints ℝ (closedBall a r) := fun _ hx ↦ by
  rw [← frontier_closedBall', frontier, closure_closedBall] at hx
  exact (_root_.strictConvex_closedBall ℝ _ _).mem_extremePoints_of_mem_sdiff_interior hx

end Normed
