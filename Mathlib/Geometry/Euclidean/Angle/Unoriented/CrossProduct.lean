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
-/

open Matrix Real WithLp

namespace InnerProductGeometry

open scoped RealInnerProductSpace

/-- The L2 norm of the cross product of two real vectors (of type `EuclideanSpace ℝ (Fin 3)`)
equals the product of their individual norms times the sine of the angle between them. -/
lemma norm_ofLp_crossProduct (a b : EuclideanSpace ℝ (Fin 3)) :
    ‖toLp 2 (ofLp a ×₃ ofLp b)‖ = ‖a‖ * ‖b‖ * sin (angle a b) := by
  have := sin_angle_nonneg a b
  refine sq_eq_sq₀ (by positivity) (by positivity) |>.mp ?_
  trans ‖a‖^2 * ‖b‖^2 - ⟪a, b⟫ ^ 2
  · simp_rw [norm_sq_eq_re_inner (𝕜 := ℝ), EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      RCLike.re_to_real, WithLp.ofLp_toLp, cross_dot_cross,
      dotProduct_comm (ofLp b) (ofLp a), sq]
  · linear_combination (‖a‖ * ‖b‖) ^ 2 * (sin_sq_add_cos_sq (angle a b)).symm +
      congrArg (· ^ 2) (cos_angle_mul_norm_mul_norm a b)

@[deprecated norm_ofLp_crossProduct (since := "2025-05-04")]
theorem norm_withLpEquiv_crossProduct (a b : EuclideanSpace ℝ (Fin 3)) :
    ‖(WithLp.equiv 2 (Fin 3 → ℝ)).symm (WithLp.equiv _ _ a ×₃ WithLp.equiv _ _ b)‖ =
    ‖a‖ * ‖b‖ * sin (angle a b) := norm_ofLp_crossProduct ..

/-- The L2 norm of the cross product of two real vectors (of type `Fin 3 → R`) equals the product
of their individual L2 norms times the sine of the angle between them. -/
lemma norm_toLp_symm_crossProduct (a b : Fin 3 → ℝ) :
    ‖toLp 2 (a ×₃ b)‖ = ‖toLp 2 a‖ * ‖toLp 2 b‖ * sin (angle (toLp 2 a) (toLp 2 b)) := by
  simp [← norm_ofLp_crossProduct (toLp 2 a) (toLp 2 b)]

/-- The L2 norm of the cross product of two real vectors (of type `Fin 3 → R`) equals the product
of their individual L2 norms times the sine of the angle between them. -/
@[deprecated norm_toLp_symm_crossProduct (since := "2025-05-04")]
theorem norm_withLpEquiv_symm_crossProduct (a b : Fin 3 → ℝ) :
    ‖(WithLp.equiv 2 (Fin 3 → ℝ)).symm (a ×₃ b)‖ =
    ‖(WithLp.equiv 2 (Fin 3 → ℝ)).symm a‖ * ‖(WithLp.equiv 2 (Fin 3 → ℝ)).symm b‖ *
      sin (angle ((WithLp.equiv 2 (Fin 3 → ℝ)).symm a) ((WithLp.equiv 2 (Fin 3 → ℝ)).symm b)) :=
  norm_toLp_symm_crossProduct ..

end InnerProductGeometry
