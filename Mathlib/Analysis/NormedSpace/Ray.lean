/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Yaël Dillies
-/
import Mathlib.LinearAlgebra.Ray
import Mathlib.Analysis.NormedSpace.Real

#align_import analysis.normed_space.ray from "leanprover-community/mathlib"@"92ca63f0fb391a9ca5f22d2409a6080e786d99f7"

/-!
# Rays in a real normed vector space

In this file we prove some lemmas about the `SameRay` predicate in case of a real normed space. In
this case, for two vectors `x y` in the same ray, the norm of their sum is equal to the sum of their
norms and `‖y‖ • x = ‖x‖ • y`.
-/


open Real

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*}
[NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SameRay

variable {x y : E}

/-- If `x` and `y` are on the same ray, then the triangle inequality becomes the equality: the norm
of `x + y` is the sum of the norms of `x` and `y`. The converse is true for a strictly convex
space. -/
theorem norm_add (h : SameRay ℝ x y) : ‖x + y‖ = ‖x‖ + ‖y‖ := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  rw [← add_smul, norm_smul_of_nonneg (add_nonneg ha hb), norm_smul_of_nonneg ha,
    norm_smul_of_nonneg hb, add_mul]
#align same_ray.norm_add SameRay.norm_add

theorem norm_sub (h : SameRay ℝ x y) : ‖x - y‖ = |‖x‖ - ‖y‖| := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  wlog hab : b ≤ a generalizing a b with H
  · rw [SameRay.sameRay_comm] at h
    rw [norm_sub_rev, abs_sub_comm]
    exact H b a hb ha h (le_of_not_le hab)
  rw [← sub_nonneg] at hab
  rw [← sub_smul, norm_smul_of_nonneg hab, norm_smul_of_nonneg ha, norm_smul_of_nonneg hb, ←
    sub_mul, abs_of_nonneg (mul_nonneg hab (norm_nonneg _))]
#align same_ray.norm_sub SameRay.norm_sub

theorem norm_smul_eq (h : SameRay ℝ x y) : ‖x‖ • y = ‖y‖ • x := by
  rcases h.exists_eq_smul with ⟨u, a, b, ha, hb, -, rfl, rfl⟩
  simp only [norm_smul_of_nonneg, *, mul_smul]
  rw [smul_comm, smul_comm b, smul_comm a b u]
#align same_ray.norm_smul_eq SameRay.norm_smul_eq

end SameRay

variable {x y : F}

theorem norm_injOn_ray_left (hx : x ≠ 0) : { y | SameRay ℝ x y }.InjOn norm := by
  rintro y hy z hz h
  rcases hy.exists_nonneg_left hx with ⟨r, hr, rfl⟩
  rcases hz.exists_nonneg_left hx with ⟨s, hs, rfl⟩
  rw [norm_smul, norm_smul, mul_left_inj' (norm_ne_zero_iff.2 hx), norm_of_nonneg hr,
    norm_of_nonneg hs] at h
  rw [h]
#align norm_inj_on_ray_left norm_injOn_ray_left

theorem norm_injOn_ray_right (hy : y ≠ 0) : { x | SameRay ℝ x y }.InjOn norm := by
  simpa only [SameRay.sameRay_comm] using norm_injOn_ray_left hy
#align norm_inj_on_ray_right norm_injOn_ray_right

theorem sameRay_iff_norm_smul_eq : SameRay ℝ x y ↔ ‖x‖ • y = ‖y‖ • x :=
  ⟨SameRay.norm_smul_eq, fun h =>
    or_iff_not_imp_left.2 fun hx =>
      or_iff_not_imp_left.2 fun hy => ⟨‖y‖, ‖x‖, norm_pos_iff.2 hy, norm_pos_iff.2 hx, h.symm⟩⟩
#align same_ray_iff_norm_smul_eq sameRay_iff_norm_smul_eq

/-- Two nonzero vectors `x y` in a real normed space are on the same ray if and only if the unit
vectors `‖x‖⁻¹ • x` and `‖y‖⁻¹ • y` are equal. -/
theorem sameRay_iff_inv_norm_smul_eq_of_ne (hx : x ≠ 0) (hy : y ≠ 0) :
    SameRay ℝ x y ↔ ‖x‖⁻¹ • x = ‖y‖⁻¹ • y := by
  rw [inv_smul_eq_iff₀, smul_comm, eq_comm, inv_smul_eq_iff₀, sameRay_iff_norm_smul_eq] <;>
    rwa [norm_ne_zero_iff]
#align same_ray_iff_inv_norm_smul_eq_of_ne sameRay_iff_inv_norm_smul_eq_of_ne

alias ⟨SameRay.inv_norm_smul_eq, _⟩ := sameRay_iff_inv_norm_smul_eq_of_ne
#align same_ray.inv_norm_smul_eq SameRay.inv_norm_smul_eq

/-- Two vectors `x y` in a real normed space are on the ray if and only if one of them is zero or
the unit vectors `‖x‖⁻¹ • x` and `‖y‖⁻¹ • y` are equal. -/
theorem sameRay_iff_inv_norm_smul_eq : SameRay ℝ x y ↔ x = 0 ∨ y = 0 ∨ ‖x‖⁻¹ • x = ‖y‖⁻¹ • y := by
  rcases eq_or_ne x 0 with (rfl | hx); · simp [SameRay.zero_left]
  rcases eq_or_ne y 0 with (rfl | hy); · simp [SameRay.zero_right]
  simp only [sameRay_iff_inv_norm_smul_eq_of_ne hx hy, *, false_or_iff]
#align same_ray_iff_inv_norm_smul_eq sameRay_iff_inv_norm_smul_eq

/-- Two vectors of the same norm are on the same ray if and only if they are equal. -/
theorem sameRay_iff_of_norm_eq (h : ‖x‖ = ‖y‖) : SameRay ℝ x y ↔ x = y := by
  obtain rfl | hy := eq_or_ne y 0
  · rw [norm_zero, norm_eq_zero] at h
    exact iff_of_true (SameRay.zero_right _) h
  · exact ⟨fun hxy => norm_injOn_ray_right hy hxy SameRay.rfl h, fun hxy => hxy ▸ SameRay.rfl⟩
#align same_ray_iff_of_norm_eq sameRay_iff_of_norm_eq

theorem not_sameRay_iff_of_norm_eq (h : ‖x‖ = ‖y‖) : ¬SameRay ℝ x y ↔ x ≠ y :=
  (sameRay_iff_of_norm_eq h).not
#align not_same_ray_iff_of_norm_eq not_sameRay_iff_of_norm_eq

/-- If two points on the same ray have the same norm, then they are equal. -/
theorem SameRay.eq_of_norm_eq (h : SameRay ℝ x y) (hn : ‖x‖ = ‖y‖) : x = y :=
  (sameRay_iff_of_norm_eq hn).mp h
#align same_ray.eq_of_norm_eq SameRay.eq_of_norm_eq

/-- The norms of two vectors on the same ray are equal if and only if they are equal. -/
theorem SameRay.norm_eq_iff (h : SameRay ℝ x y) : ‖x‖ = ‖y‖ ↔ x = y :=
  ⟨h.eq_of_norm_eq, fun h => h ▸ rfl⟩
#align same_ray.norm_eq_iff SameRay.norm_eq_iff
