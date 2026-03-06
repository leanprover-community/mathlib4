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
the sphere is equal to the extreme points of the closed ball. -/

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

open Filter in
open scoped Topology in
theorem disjoint_interior_extremePoints {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [Nontrivial E]
    (S : Set E) : Disjoint (interior S) (extremePoints ℝ S) := by
  refine Set.disjoint_iff.mpr fun x ⟨x_int, x_ext⟩ ↦ ?_
  rw [mem_interior_iff_mem_nhds] at x_int
  have h₁ : ∀ᶠ v in 𝓝[≠] 0, x - v ∈ S :=
    (tendsto_inf_left <| (continuous_sub_left _).tendsto' _ _ (sub_zero _)).eventually x_int
  have h₂ : ∀ᶠ v in 𝓝[≠] 0, x + v ∈ S :=
    (tendsto_inf_left <| (continuous_add_left _).tendsto' _ _ (add_zero _)).eventually x_int
  obtain ⟨v, ⟨hv₁, hv₂⟩, (v_ne : v ≠ 0)⟩ := h₁.and h₂ |>.and eventually_mem_nhdsWithin |>.exists
  have key : x ∈ openSegment ℝ (x - v) (x + v) := mem_openSegment_sub_add _ _ _
  grind only [x_ext.2 hv₁ hv₂ key]

/-- In a nontrivial normed space, the extreme points of the closed ball is contained in
the sphere. -/
theorem extremePoints_closedBall_subset_sphere [Nontrivial A] {r : ℝ} {x : A} :
    extremePoints ℝ (closedBall x r) ⊆ sphere x r := by
  rw [← closedBall_diff_ball, subset_diff, ← interior_closedBall' _]
  exact ⟨extremePoints_subset, disjoint_interior_extremePoints _ |>.symm⟩

theorem StrictConvexSpace.extremePoints_closedBall_eq_sphere [Nontrivial A] {r : ℝ} {x : A}
    [StrictConvexSpace ℝ A] : extremePoints ℝ (closedBall x r) = sphere x r :=
  antisymm extremePoints_closedBall_subset_sphere sphere_subset_extremePoints_closedBall'

end Normed
