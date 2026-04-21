/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.StrictConvexSpace

import Mathlib.Algebra.CharP.Invertible

/-! # Extreme points of (strictly convex) sets

This file collects some results of extreme points of (strictly convex) sets.

## Main results
* `disjoint_interior_extremePoints`: the interior and extreme points of a set in a
  nontrivial topological vector space are disjoint.
* `StrictConvex.diff_interior_subset_extremePoints`:
  when `C` is a strictly convex set then `C \ interior C ⊆ extremePoints 𝕜 C`.
* `StrictConvex.extremePoints_eq_diff_interior`: the extreme points of a strictly convex set `S`
  in nontrivial normed space is exactly `S \ interior S`.

Corollaries of the above is that, in a nontrivial normed space, the extreme points of the
closed ball is contained in the sphere (see `extremePoints_closedBall_subset_sphere`).
And in a nontrivial strictly convex space, the extreme points of the closed ball is exactly the
sphere (see `StrictConvexSpace.extremePoints_closedBall_eq_sphere`). -/
set_option backward.defeqAttrib.useBackward true

public section

open Set Metric

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
    (tendsto_inf_left <| (continuous_const_add _).tendsto' _ _ (add_zero _)).eventually x_int
  obtain ⟨v, ⟨hv₁, hv₂⟩, (v_ne : v ≠ 0)⟩ := h₁.and h₂ |>.and eventually_mem_nhdsWithin |>.exists
  have key : x ∈ openSegment ℝ (x - v) (x + v) := mem_openSegment_sub_add _ _
  grind only [x_ext.2 hv₁ hv₂ key]

lemma StrictConvex.diff_interior_subset_extremePoints {𝕜 A : Type*} [Semiring 𝕜]
    [PartialOrder 𝕜] [AddCommMonoid A] [Module 𝕜 A] [TopologicalSpace A] {C : Set A}
    (hc : StrictConvex 𝕜 C) : C \ interior C ⊆ extremePoints 𝕜 C := by
  refine fun x hx ↦ ⟨hx.1, fun y hy z hz ⟨a, b, ha, hb, hab, hxab⟩ ↦ ?_⟩
  have hyz : y = z := by
    by_contra
    exact hx.2 <| hxab ▸ hc hy hz this ha hb hab
  rwa [← hyz, ← add_smul, hab, one_smul] at hxab

section Normed
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- In a nontrivial normed space, the extreme points of the closed ball is contained in
the sphere. -/
theorem extremePoints_closedBall_subset_sphere [Nontrivial A] {x : A} {r : ℝ} :
    extremePoints ℝ (closedBall x r) ⊆ sphere x r := by
  rw [← closedBall_diff_ball, subset_diff, ← interior_closedBall' _]
  exact ⟨extremePoints_subset, disjoint_interior_extremePoints _ |>.symm⟩

theorem StrictConvex.extremePoints_eq_diff_interior [Nontrivial A] {S : Set A}
    (hS : StrictConvex ℝ S) : extremePoints ℝ S = S \ interior S :=
  antisymm (subset_diff.mpr ⟨extremePoints_subset, disjoint_interior_extremePoints _ |>.symm⟩)
    hS.diff_interior_subset_extremePoints

/-- In a strictly convex space, the sphere is contained in the extreme points of the closed ball
when the radius is nonzero.
In a nontrivial space, they are equal, see `extremePoints_closedBall_eq_sphere`. -/
lemma StrictConvexSpace.sphere_subset_extremePoints_closedBall [StrictConvexSpace ℝ A]
    (a : A) {r : ℝ} (hr : r ≠ 0) : sphere a r ⊆ extremePoints ℝ (closedBall a r) := fun _ hx ↦ by
  rw [← frontier_closedBall _ hr, frontier, closure_closedBall] at hx
  exact (_root_.strictConvex_closedBall ℝ _ _).diff_interior_subset_extremePoints hx

theorem StrictConvexSpace.extremePoints_closedBall_eq_sphere [Nontrivial A] {x : A} {r : ℝ}
    [StrictConvexSpace ℝ A] : extremePoints ℝ (closedBall x r) = sphere x r := by
  rw [(_root_.strictConvex_closedBall ℝ x r).extremePoints_eq_diff_interior, interior_closedBall',
    closedBall_diff_ball]

end Normed

@[simp] lemma Set.extremePoints_Icc {a b : ℝ} (hab : a ≤ b) :
    extremePoints ℝ (Icc a b) = {a, b} := by
  rw [Real.Icc_eq_closedBall, StrictConvexSpace.extremePoints_closedBall_eq_sphere]
  grind [Real.sphere_eq_pair]
