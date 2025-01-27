/-
Copyright (c) 2020 Vedant Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vedant Gupta, Thomas Browning, Eric Wieser
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Norm of cross-products

This file proves `InnerProductGeometry.norm_withLpEquiv_crossProduct`, relating the norm of the
cross-product of two real vectors with their individual norms.

## Main definitions

* `InnerProductGeometry.angle` is the undirected angle between two vectors.
-/


assert_not_exists HasFDerivAt ConformalAt

noncomputable section

open Real

open Matrix

namespace InnerProductGeometry

/- The norm of the cross product of two real vectors equals the product of their individual norms
  times the sine of the angle between them. -/
theorem norm_withLpEquiv_crossProduct (a b : EuclideanSpace ℝ (Fin 3)) :
    ‖(WithLp.equiv 2 (Fin 3 → ℝ)).symm (WithLp.equiv _ _ a ×₃ WithLp.equiv _ _ b)‖ =
    ‖a‖ * ‖b‖ * sin (angle a b) := by
  have := @sin_angle_nonneg _ _ _ a b
  refine sq_eq_sq₀ (by positivity) (by positivity) |>.mp ?_
  trans ‖a‖^2 * ‖b‖^2 - inner a b ^ 2
  · simp_rw [norm_sq_eq_inner (𝕜 := ℝ), EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      RCLike.re_to_real, Equiv.apply_symm_apply, cross_dot_cross,
      dotProduct_comm (WithLp.equiv _ _ b) (WithLp.equiv _ _ a), sq]
  · linear_combination (‖a‖ * ‖b‖) ^ 2 * (sin_sq_add_cos_sq (angle a b)).symm +
      congrArg (· ^ 2) (cos_angle_mul_norm_mul_norm a b)

end InnerProductGeometry
