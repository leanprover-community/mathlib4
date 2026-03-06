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

theorem not_mem_extremePoints_of_mem_interior {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] [Nontrivial E]
    {S : Set E} {x : E} (hx : x ∈ interior S) : x ∉ extremePoints ℝ S := fun h ↦ by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  let f (t : ℝ) : E := x + t • v
  obtain ⟨ε, hε, hεb⟩ : ∃ ε > 0, f '' ball 0 ε ⊆ interior S := by
    simp_rw [image_subset_iff]
    refine Metric.mem_nhds_iff.mp <| (by fun_prop : Continuous f).continuousAt ?_
    simp only [zero_smul, add_zero, interior_mem_nhds, f]
    exact mem_interior_iff_mem_nhds.mp hx
  have : f (ε / 2) ≠ f (-ε / 2) := by
    simp only [ne_eq, neg_div, neg_smul, add_right_inj, f]
    rw [← sub_eq_zero, sub_neg_eq_add, ← two_smul ℝ]
    simp [hv, hε.ne']
  have := mem_extremePoints.mp h |>.2 (f (ε / 2)) (interior_subset (hεb (by simp; grind)))
    (f (-ε / 2)) (interior_subset (hεb (by simp; grind))) ⟨2⁻¹, 2⁻¹, ?_⟩
  · grind
  · simp [← one_div, ← smul_add, f, neg_div, add_assoc, ← two_smul ℝ, smul_smul, mul_one_div_cancel]

/-- In a nontrivial normed space, the extreme points of the closed unit ball is contained in
the unit sphere. -/
theorem extremePoints_closedUnitBall_subset_unitSphere [Nontrivial A] :
    extremePoints ℝ (closedBall (0 : A) 1) ⊆ sphere 0 1 := fun x hx ↦ by
  have h : x ≠ 0 := fun h ↦
    not_mem_extremePoints_of_mem_interior (by simp [h, interior_closedBall]) hx
  simp only [mem_extremePoints, mem_closedBall, dist_zero_right] at hx
  by_contra!
  refine h (@hx.2 (‖x‖⁻¹ • x) ?_ 0 (by simp) ⟨‖x‖, 1 - ‖x‖, by simp_all, ?_, ?_⟩).2.symm
  on_goal 2 => grind [mem_sphere_zero_iff_norm]
  all_goals simp [norm_smul, norm_ne_zero_iff.mpr h]

theorem StrictConvexSpace.extremePoints_closedUnitBall_eq_unitSphere [Nontrivial A]
    [StrictConvexSpace ℝ A] : extremePoints ℝ (closedBall (0 : A) 1) = sphere 0 1 :=
  antisymm extremePoints_closedUnitBall_subset_unitSphere sphere_subset_extremePoints_closedBall'

end Normed
