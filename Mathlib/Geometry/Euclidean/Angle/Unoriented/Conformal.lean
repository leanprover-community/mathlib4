/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import Mathlib.Analysis.Calculus.Conformal.NormedSpace
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

#align_import geometry.euclidean.angle.unoriented.conformal from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Angles and conformal maps

This file proves that conformal maps preserve angles.

-/


namespace InnerProductGeometry

variable {E F : Type*}

variable [NormedAddCommGroup E] [NormedAddCommGroup F]

variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

theorem IsConformalMap.preserves_angle {f' : E →L[ℝ] F} (h : IsConformalMap f') (u v : E) :
    angle (f' u) (f' v) = angle u v := by
  obtain ⟨c, hc, li, rfl⟩ := h
  -- ⊢ angle (↑(c • LinearIsometry.toContinuousLinearMap li) u) (↑(c • LinearIsomet …
  exact (angle_smul_smul hc _ _).trans (li.angle_map _ _)
  -- 🎉 no goals
#align inner_product_geometry.is_conformal_map.preserves_angle InnerProductGeometry.IsConformalMap.preserves_angle

/-- If a real differentiable map `f` is conformal at a point `x`,
    then it preserves the angles at that point. -/
theorem ConformalAt.preserves_angle {f : E → F} {x : E} {f' : E →L[ℝ] F} (h : HasFDerivAt f f' x)
    (H : ConformalAt f x) (u v : E) : angle (f' u) (f' v) = angle u v :=
  let ⟨_, h₁, c⟩ := H
  h₁.unique h ▸ IsConformalMap.preserves_angle c u v
#align inner_product_geometry.conformal_at.preserves_angle InnerProductGeometry.ConformalAt.preserves_angle

end InnerProductGeometry
