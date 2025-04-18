/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# (Strict) convexity and linear isometries

In this file we prove some basic lemmas about (strict) convexity and linear isometries.

## TODO

- generalize `StrictConvex.linearIsometry_preimage` etc to `LinearMapClass`;

-/

open Function Set Metric
open scoped Convex

variable {E E' F F' : Type*}
  [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

lemma StrictConvex.linearIsometry_preimage {s : Set F} (hs : StrictConvex ℝ s) (e : E' →ₗᵢ[ℝ] F) :
    StrictConvex ℝ (e ⁻¹' s) :=
  hs.linear_preimage _ e.continuous e.injective

@[simp]
lemma LinearIsometryEquiv.strictConvex_preimage {s : Set F} (e : E ≃ₗᵢ[ℝ] F) :
    StrictConvex ℝ (e ⁻¹' s) ↔ StrictConvex ℝ s :=
  ⟨fun h ↦ LeftInverse.preimage_preimage e.right_inv s ▸
    h.linear_preimage e.symm.toLinearIsometry.toLinearMap e.symm.continuous e.symm.injective,
    fun h ↦ h.linear_preimage e.toLinearIsometry.toLinearMap e.continuous e.injective⟩

@[simp]
lemma LinearIsometryEquiv.strictConvex_image {s : Set E} (e : E ≃ₗᵢ[ℝ] F) :
    StrictConvex ℝ (e '' s) ↔ StrictConvex ℝ s := by
  rw [e.image_eq_preimage, e.symm.strictConvex_preimage]

protected lemma LinearIsometryEquiv.strictConvexSpace_iff (e : E' ≃ₗᵢ[ℝ] F') :
    StrictConvexSpace ℝ E' ↔ StrictConvexSpace ℝ F' := by
  simp only [strictConvexSpace_iff, ← map_zero e, ← e.image_closedBall, e.strictConvex_image]

lemma LinearIsometry.strictConvexSpace_range_iff (e : E' →ₗᵢ[ℝ] F') :
    StrictConvexSpace ℝ (LinearMap.range e) ↔ StrictConvexSpace ℝ E' :=
  e.equivRange.strictConvexSpace_iff.symm

instance LinearIsometry.strictConvexSpace_range [StrictConvexSpace ℝ E'] (e : E' →ₗᵢ[ℝ] F') :
    StrictConvexSpace ℝ (LinearMap.range e) :=
  e.strictConvexSpace_range_iff.mpr ‹_›

/-- A vector subspace of a strict convex space is a strict convex space.

This instance has priority 900
to make sure that instances like `LinearIsometry.strictConvexSpace_range`
are tried before this one. -/
instance (priority := 900) Submodule.instStrictConvexSpace [StrictConvexSpace ℝ E']
    (p : Submodule ℝ E') : StrictConvexSpace ℝ p where
  strictConvex_closedBall r hr := by
    rw [← p.subtypeₗᵢ.isometry.preimage_closedBall]
    exact (strictConvex_closedBall _ _ _).linearIsometry_preimage _
