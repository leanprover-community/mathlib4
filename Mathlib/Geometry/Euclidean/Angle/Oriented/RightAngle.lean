/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

#align_import geometry.euclidean.angle.oriented.right_angle from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Oriented angles in right-angled triangles.

This file proves basic geometrical results about distances and oriented angles in (possibly
degenerate) right-angled triangles in real inner product spaces and Euclidean affine spaces.

-/


noncomputable section

open scoped EuclideanGeometry

open scoped Real

open scoped RealInnerProductSpace

namespace Orientation

open FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable [hd2 : Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arccos (‖x‖ / ‖x + y‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_add_eq_arccos_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]
#align orientation.oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two Orientation.oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arccos (‖y‖ / ‖x + y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ oangle (-o) y (x + y) = ↑(Real.arccos (‖y‖ / ‖x + y‖))
  rw [add_comm]
  -- ⊢ oangle (-o) y (y + x) = ↑(Real.arccos (‖y‖ / ‖y + x‖))
  exact (-o).oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two Orientation.oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two Orientation.oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arcsin (‖x‖ / ‖x + y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ oangle (-o) y (x + y) = ↑(Real.arcsin (‖x‖ / ‖x + y‖))
  rw [add_comm]
  -- ⊢ oangle (-o) y (y + x) = ↑(Real.arcsin (‖x‖ / ‖y + x‖))
  exact (-o).oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two Orientation.oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arctan (‖y‖ / ‖x‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (o.left_ne_zero_of_oangle_eq_pi_div_two h)]
#align orientation.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two Orientation.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arctan (‖x‖ / ‖y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ oangle (-o) y (x + y) = ↑(Real.arctan (‖x‖ / ‖y‖))
  rw [add_comm]
  -- ⊢ oangle (-o) y (y + x) = ↑(Real.arctan (‖x‖ / ‖y‖))
  exact (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two Orientation.oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle x (x + y)) = ‖x‖ / ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]
#align orientation.cos_oangle_add_right_of_oangle_eq_pi_div_two Orientation.cos_oangle_add_right_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x + y) y) = ‖y‖ / ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ Real.Angle.cos (oangle (-o) y (x + y)) = ‖y‖ / ‖x + y‖
  rw [add_comm]
  -- ⊢ Real.Angle.cos (oangle (-o) y (y + x)) = ‖y‖ / ‖y + x‖
  exact (-o).cos_oangle_add_right_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.cos_oangle_add_left_of_oangle_eq_pi_div_two Orientation.cos_oangle_add_left_of_oangle_eq_pi_div_two

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle x (x + y)) = ‖y‖ / ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.sin_oangle_add_right_of_oangle_eq_pi_div_two Orientation.sin_oangle_add_right_of_oangle_eq_pi_div_two

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle (x + y) y) = ‖x‖ / ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ Real.Angle.sin (oangle (-o) y (x + y)) = ‖x‖ / ‖x + y‖
  rw [add_comm]
  -- ⊢ Real.Angle.sin (oangle (-o) y (y + x)) = ‖x‖ / ‖y + x‖
  exact (-o).sin_oangle_add_right_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.sin_oangle_add_left_of_oangle_eq_pi_div_two Orientation.sin_oangle_add_left_of_oangle_eq_pi_div_two

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle x (x + y)) = ‖y‖ / ‖x‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.tan_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]
#align orientation.tan_oangle_add_right_of_oangle_eq_pi_div_two Orientation.tan_oangle_add_right_of_oangle_eq_pi_div_two

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle (x + y) y) = ‖x‖ / ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ Real.Angle.tan (oangle (-o) y (x + y)) = ‖x‖ / ‖y‖
  rw [add_comm]
  -- ⊢ Real.Angle.tan (oangle (-o) y (y + x)) = ‖x‖ / ‖y‖
  exact (-o).tan_oangle_add_right_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.tan_oangle_add_left_of_oangle_eq_pi_div_two Orientation.tan_oangle_add_left_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle x (x + y)) * ‖x + y‖ = ‖x‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]
#align orientation.cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two Orientation.cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle (x + y) y) * ‖x + y‖ = ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ Real.Angle.cos (oangle (-o) y (x + y)) * ‖x + y‖ = ‖y‖
  rw [add_comm]
  -- ⊢ Real.Angle.cos (oangle (-o) y (y + x)) * ‖y + x‖ = ‖y‖
  exact (-o).cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two Orientation.cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle x (x + y)) * ‖x + y‖ = ‖y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]
#align orientation.sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two Orientation.sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle (x + y) y) * ‖x + y‖ = ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ Real.Angle.sin (oangle (-o) y (x + y)) * ‖x + y‖ = ‖x‖
  rw [add_comm]
  -- ⊢ Real.Angle.sin (oangle (-o) y (y + x)) * ‖y + x‖ = ‖x‖
  exact (-o).sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two Orientation.sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle x (x + y)) * ‖x‖ = ‖y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.tan_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two Orientation.tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle (x + y) y) * ‖y‖ = ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ Real.Angle.tan (oangle (-o) y (x + y)) * ‖y‖ = ‖x‖
  rw [add_comm]
  -- ⊢ Real.Angle.tan (oangle (-o) y (y + x)) * ‖y‖ = ‖x‖
  exact (-o).tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two Orientation.tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.cos (o.oangle x (x + y)) = ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.norm_div_cos_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two Orientation.norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.cos (o.oangle (x + y) y) = ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ ‖y‖ / Real.Angle.cos (oangle (-o) y (x + y)) = ‖x + y‖
  rw [add_comm]
  -- ⊢ ‖y‖ / Real.Angle.cos (oangle (-o) y (y + x)) = ‖y + x‖
  exact (-o).norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two Orientation.norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.sin (o.oangle x (x + y)) = ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.norm_div_sin_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inr (o.right_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two Orientation.norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.sin (o.oangle (x + y) y) = ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ ‖x‖ / Real.Angle.sin (oangle (-o) y (x + y)) = ‖x + y‖
  rw [add_comm]
  -- ⊢ ‖x‖ / Real.Angle.sin (oangle (-o) y (y + x)) = ‖y + x‖
  exact (-o).norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two Orientation.norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.tan (o.oangle x (x + y)) = ‖x‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.norm_div_tan_angle_add_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inr (o.right_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two Orientation.norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.tan (o.oangle (x + y) y) = ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ ‖x‖ / Real.Angle.tan (oangle (-o) y (x + y)) = ‖y‖
  rw [add_comm]
  -- ⊢ ‖x‖ / Real.Angle.tan (oangle (-o) y (y + x)) = ‖y‖
  exact (-o).norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two Orientation.norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
theorem oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arccos (‖y‖ / ‖y - x‖) := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_sub_eq_arccos_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]
#align orientation.oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two Orientation.oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
theorem oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arccos (‖x‖ / ‖x - y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ oangle (-o) x (x - y) = ↑(Real.arccos (‖x‖ / ‖x - y‖))
  exact (-o).oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two Orientation.oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
theorem oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arcsin (‖x‖ / ‖y - x‖) := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_sub_eq_arcsin_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two Orientation.oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
theorem oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arcsin (‖y‖ / ‖x - y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ oangle (-o) x (x - y) = ↑(Real.arcsin (‖y‖ / ‖x - y‖))
  exact (-o).oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two Orientation.oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
theorem oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arctan (‖x‖ / ‖y‖) := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_sub_eq_arctan_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h) (o.right_ne_zero_of_oangle_eq_pi_div_two h)]
#align orientation.oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two Orientation.oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
theorem oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arctan (‖y‖ / ‖x‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ oangle (-o) x (x - y) = ↑(Real.arctan (‖y‖ / ‖x‖))
  exact (-o).oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two Orientation.oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle y (y - x)) = ‖y‖ / ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]
#align orientation.cos_oangle_sub_right_of_oangle_eq_pi_div_two Orientation.cos_oangle_sub_right_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x - y) x) = ‖x‖ / ‖x - y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ Real.Angle.cos (oangle (-o) x (x - y)) = ‖x‖ / ‖x - y‖
  exact (-o).cos_oangle_sub_right_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.cos_oangle_sub_left_of_oangle_eq_pi_div_two Orientation.cos_oangle_sub_left_of_oangle_eq_pi_div_two

/-- The sine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle y (y - x)) = ‖x‖ / ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.sin_oangle_sub_right_of_oangle_eq_pi_div_two Orientation.sin_oangle_sub_right_of_oangle_eq_pi_div_two

/-- The sine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle (x - y) x) = ‖y‖ / ‖x - y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ Real.Angle.sin (oangle (-o) x (x - y)) = ‖y‖ / ‖x - y‖
  exact (-o).sin_oangle_sub_right_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.sin_oangle_sub_left_of_oangle_eq_pi_div_two Orientation.sin_oangle_sub_left_of_oangle_eq_pi_div_two

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle y (y - x)) = ‖x‖ / ‖y‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.tan_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]
#align orientation.tan_oangle_sub_right_of_oangle_eq_pi_div_two Orientation.tan_oangle_sub_right_of_oangle_eq_pi_div_two

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle (x - y) x) = ‖y‖ / ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ Real.Angle.tan (oangle (-o) x (x - y)) = ‖y‖ / ‖x‖
  exact (-o).tan_oangle_sub_right_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.tan_oangle_sub_left_of_oangle_eq_pi_div_two Orientation.tan_oangle_sub_left_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
theorem cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle y (y - x)) * ‖y - x‖ = ‖y‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]
#align orientation.cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two Orientation.cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
theorem cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle (x - y) x) * ‖x - y‖ = ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ Real.Angle.cos (oangle (-o) x (x - y)) * ‖x - y‖ = ‖x‖
  exact (-o).cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two Orientation.cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
theorem sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle y (y - x)) * ‖y - x‖ = ‖x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]
#align orientation.sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two Orientation.sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
theorem sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle (x - y) x) * ‖x - y‖ = ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ Real.Angle.sin (oangle (-o) x (x - y)) * ‖x - y‖ = ‖y‖
  exact (-o).sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two Orientation.sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side, version subtracting vectors. -/
theorem tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle y (y - x)) * ‖y‖ = ‖x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.tan_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two Orientation.tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side, version subtracting vectors. -/
theorem tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle (x - y) x) * ‖x‖ = ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ Real.Angle.tan (oangle (-o) x (x - y)) * ‖x‖ = ‖y‖
  exact (-o).tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two Orientation.tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse, version subtracting vectors. -/
theorem norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.cos (o.oangle y (y - x)) = ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.norm_div_cos_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two Orientation.norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse, version subtracting vectors. -/
theorem norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.cos (o.oangle (x - y) x) = ‖x - y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ ‖x‖ / Real.Angle.cos (oangle (-o) x (x - y)) = ‖x - y‖
  exact (-o).norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two Orientation.norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse, version subtracting vectors. -/
theorem norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.sin (o.oangle y (y - x)) = ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.norm_div_sin_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inr (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two Orientation.norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse, version subtracting vectors. -/
theorem norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.sin (o.oangle (x - y) x) = ‖x - y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ ‖y‖ / Real.Angle.sin (oangle (-o) x (x - y)) = ‖x - y‖
  exact (-o).norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two Orientation.norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side, version subtracting vectors. -/
theorem norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.tan (o.oangle y (y - x)) = ‖y‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.norm_div_tan_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inr (o.left_ne_zero_of_oangle_eq_pi_div_two h))]
#align orientation.norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two Orientation.norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side, version subtracting vectors. -/
theorem norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.tan (o.oangle (x - y) x) = ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  -- ⊢ ‖y‖ / Real.Angle.tan (oangle (-o) x (x - y)) = ‖x‖
  exact (-o).norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two h
  -- 🎉 no goals
#align orientation.norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two Orientation.norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`. -/
theorem oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle x (x + r • o.rotation (π / 2 : ℝ) x) = Real.arctan r := by
  rcases lt_trichotomy r 0 with (hr | rfl | hr)
  · have ha : o.oangle x (r • o.rotation (π / 2 : ℝ) x) = -(π / 2 : ℝ) := by
      rw [o.oangle_smul_right_of_neg _ _ hr, o.oangle_neg_right h, o.oangle_rotation_self_right h, ←
        sub_eq_zero, add_comm, sub_neg_eq_add, ← Real.Angle.coe_add, ← Real.Angle.coe_add,
        add_assoc, add_halves, ← two_mul, Real.Angle.coe_two_pi]
      simpa using h
    -- Porting note: if the type is not given in `neg_neg` then Lean "forgets" about the instance
    -- `Neg (Orientation ℝ V (Fin 2))`
    rw [← neg_inj, ← oangle_neg_orientation_eq_neg, @neg_neg Real.Angle] at ha
    -- ⊢ oangle o x (x + r • ↑(rotation o ↑(π / 2)) x) = ↑(Real.arctan r)
    rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj, oangle_rev,
      (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two ha, norm_smul,
      LinearIsometryEquiv.norm_map, mul_div_assoc, div_self (norm_ne_zero_iff.2 h), mul_one,
      Real.norm_eq_abs, abs_of_neg hr, Real.arctan_neg, Real.Angle.coe_neg, neg_neg]
  · rw [zero_smul, add_zero, oangle_self, Real.arctan_zero, Real.Angle.coe_zero]
    -- 🎉 no goals
  · have ha : o.oangle x (r • o.rotation (π / 2 : ℝ) x) = (π / 2 : ℝ) := by
      rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right h]
    rw [o.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two ha, norm_smul,
      LinearIsometryEquiv.norm_map, mul_div_assoc, div_self (norm_ne_zero_iff.2 h), mul_one,
      Real.norm_eq_abs, abs_of_pos hr]
#align orientation.oangle_add_right_smul_rotation_pi_div_two Orientation.oangle_add_right_smul_rotation_pi_div_two

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`. -/
theorem oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle (x + r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x)
      = Real.arctan r⁻¹ := by
  by_cases hr : r = 0; · simp [hr]
  -- ⊢ oangle o (x + r • ↑(rotation o ↑(π / 2)) x) (r • ↑(rotation o ↑(π / 2)) x) = …
                         -- 🎉 no goals
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj, ←
    neg_neg ((π / 2 : ℝ) : Real.Angle), ← rotation_neg_orientation_eq_neg, add_comm]
  have hx : x = r⁻¹ • (-o).rotation (π / 2 : ℝ) (r • (-o).rotation (-(π / 2 : ℝ)) x) := by simp [hr]
  -- ⊢ oangle (-o) (r • ↑(rotation (-o) (-↑(π / 2))) x) (r • ↑(rotation (-o) (-↑(π  …
  nth_rw 3 [hx]
  -- ⊢ oangle (-o) (r • ↑(rotation (-o) (-↑(π / 2))) x) (r • ↑(rotation (-o) (-↑(π  …
  refine' (-o).oangle_add_right_smul_rotation_pi_div_two _ _
  -- ⊢ r • ↑(rotation (-o) (-↑(π / 2))) x ≠ 0
  simp [hr, h]
  -- 🎉 no goals
#align orientation.oangle_add_left_smul_rotation_pi_div_two Orientation.oangle_add_left_smul_rotation_pi_div_two

/-- The tangent of an angle in a right-angled triangle, where one side is a multiple of a
rotation of another by `π / 2`. -/
theorem tan_oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    Real.Angle.tan (o.oangle x (x + r • o.rotation (π / 2 : ℝ) x)) = r := by
  rw [o.oangle_add_right_smul_rotation_pi_div_two h, Real.Angle.tan_coe, Real.tan_arctan]
  -- 🎉 no goals
#align orientation.tan_oangle_add_right_smul_rotation_pi_div_two Orientation.tan_oangle_add_right_smul_rotation_pi_div_two

/-- The tangent of an angle in a right-angled triangle, where one side is a multiple of a
rotation of another by `π / 2`. -/
theorem tan_oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    Real.Angle.tan (o.oangle (x + r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x)) =
      r⁻¹ :=
  by rw [o.oangle_add_left_smul_rotation_pi_div_two h, Real.Angle.tan_coe, Real.tan_arctan]
     -- 🎉 no goals
#align orientation.tan_oangle_add_left_smul_rotation_pi_div_two Orientation.tan_oangle_add_left_smul_rotation_pi_div_two

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`, version subtracting vectors. -/
theorem oangle_sub_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle (r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x - x)
      = Real.arctan r⁻¹ := by
  by_cases hr : r = 0; · simp [hr]
  -- ⊢ oangle o (r • ↑(rotation o ↑(π / 2)) x) (r • ↑(rotation o ↑(π / 2)) x - x) = …
                         -- 🎉 no goals
  have hx : -x = r⁻¹ • o.rotation (π / 2 : ℝ) (r • o.rotation (π / 2 : ℝ) x) := by
    simp [hr, ← Real.Angle.coe_add]
  rw [sub_eq_add_neg, hx, o.oangle_add_right_smul_rotation_pi_div_two]
  -- ⊢ r • ↑(rotation o ↑(π / 2)) x ≠ 0
  simpa [hr] using h
  -- 🎉 no goals
#align orientation.oangle_sub_right_smul_rotation_pi_div_two Orientation.oangle_sub_right_smul_rotation_pi_div_two

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`, version subtracting vectors. -/
theorem oangle_sub_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle (x - r • o.rotation (π / 2 : ℝ) x) x = Real.arctan r := by
  by_cases hr : r = 0; · simp [hr]
  -- ⊢ oangle o (x - r • ↑(rotation o ↑(π / 2)) x) x = ↑(Real.arctan r)
                         -- 🎉 no goals
  have hx : x = r⁻¹ • o.rotation (π / 2 : ℝ) (-(r • o.rotation (π / 2 : ℝ) x)) := by
    simp [hr, ← Real.Angle.coe_add]
  rw [sub_eq_add_neg, add_comm]
  -- ⊢ oangle o (-(r • ↑(rotation o ↑(π / 2)) x) + x) x = ↑(Real.arctan r)
  nth_rw 3 [hx]
  -- ⊢ oangle o (-(r • ↑(rotation o ↑(π / 2)) x) + x) (r⁻¹ • ↑(rotation o ↑(π / 2)) …
  nth_rw 2 [hx]
  -- ⊢ oangle o (-(r • ↑(rotation o ↑(π / 2)) x) + r⁻¹ • ↑(rotation o ↑(π / 2)) (-( …
  rw [o.oangle_add_left_smul_rotation_pi_div_two, inv_inv]
  -- ⊢ -(r • ↑(rotation o ↑(π / 2)) x) ≠ 0
  simpa [hr] using h
  -- 🎉 no goals
#align orientation.oangle_sub_left_smul_rotation_pi_div_two Orientation.oangle_sub_left_smul_rotation_pi_div_two

end Orientation

namespace EuclideanGeometry

open FiniteDimensional

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_right_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arccos (dist p₃ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ ∡ p₂ p₃ p₁ = ↑(Real.arccos (dist p₃ p₂ / dist p₁ p₃))
  rw [oangle_eq_angle_of_sign_eq_one hs,
    angle_eq_arccos_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
#align euclidean_geometry.oangle_right_eq_arccos_of_oangle_eq_pi_div_two EuclideanGeometry.oangle_right_eq_arccos_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_left_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arccos (dist p₁ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ ∡ p₃ p₁ p₂ = ↑(Real.arccos (dist p₁ p₂ / dist p₁ p₃))
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm,
    angle_eq_arccos_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h),
    dist_comm p₁ p₃]
#align euclidean_geometry.oangle_left_eq_arccos_of_oangle_eq_pi_div_two EuclideanGeometry.oangle_left_eq_arccos_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_right_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arcsin (dist p₁ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ ∡ p₂ p₃ p₁ = ↑(Real.arcsin (dist p₁ p₂ / dist p₁ p₃))
  rw [oangle_eq_angle_of_sign_eq_one hs,
    angle_eq_arcsin_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]
#align euclidean_geometry.oangle_right_eq_arcsin_of_oangle_eq_pi_div_two EuclideanGeometry.oangle_right_eq_arcsin_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_left_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arcsin (dist p₃ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ ∡ p₃ p₁ p₂ = ↑(Real.arcsin (dist p₃ p₂ / dist p₁ p₃))
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm,
    angle_eq_arcsin_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h)),
    dist_comm p₁ p₃]
#align euclidean_geometry.oangle_left_eq_arcsin_of_oangle_eq_pi_div_two EuclideanGeometry.oangle_left_eq_arcsin_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_right_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist p₃ p₂) := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ ∡ p₂ p₃ p₁ = ↑(Real.arctan (dist p₁ p₂ / dist p₃ p₂))
  rw [oangle_eq_angle_of_sign_eq_one hs,
    angle_eq_arctan_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (right_ne_of_oangle_eq_pi_div_two h)]
#align euclidean_geometry.oangle_right_eq_arctan_of_oangle_eq_pi_div_two EuclideanGeometry.oangle_right_eq_arctan_of_oangle_eq_pi_div_two

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_left_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arctan (dist p₃ p₂ / dist p₁ p₂) := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ ∡ p₃ p₁ p₂ = ↑(Real.arctan (dist p₃ p₂ / dist p₁ p₂))
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm,
    angle_eq_arctan_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (left_ne_of_oangle_eq_pi_div_two h)]
#align euclidean_geometry.oangle_left_eq_arctan_of_oangle_eq_pi_div_two EuclideanGeometry.oangle_left_eq_arctan_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.cos (∡ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ Real.Angle.cos (∡ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
#align euclidean_geometry.cos_oangle_right_of_oangle_eq_pi_div_two EuclideanGeometry.cos_oangle_right_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ Real.Angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₂ / dist p₁ p₃
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.cos_coe,
    cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h),
    dist_comm p₁ p₃]
#align euclidean_geometry.cos_oangle_left_of_oangle_eq_pi_div_two EuclideanGeometry.cos_oangle_left_of_oangle_eq_pi_div_two

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ Real.Angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]
#align euclidean_geometry.sin_oangle_right_of_oangle_eq_pi_div_two EuclideanGeometry.sin_oangle_right_of_oangle_eq_pi_div_two

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.sin (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ Real.Angle.sin (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₃
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.sin_coe,
    sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h)),
    dist_comm p₁ p₃]
#align euclidean_geometry.sin_oangle_left_of_oangle_eq_pi_div_two EuclideanGeometry.sin_oangle_left_of_oangle_eq_pi_div_two

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.tan (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ Real.Angle.tan (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
#align euclidean_geometry.tan_oangle_right_of_oangle_eq_pi_div_two EuclideanGeometry.tan_oangle_right_of_oangle_eq_pi_div_two

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.tan (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ Real.Angle.tan (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₂
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.tan_coe,
    tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
#align euclidean_geometry.tan_oangle_left_of_oangle_eq_pi_div_two EuclideanGeometry.tan_oangle_left_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.cos (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ Real.Angle.cos (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
#align euclidean_geometry.cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two EuclideanGeometry.cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.cos (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₁ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ Real.Angle.cos (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₁ p₂
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.cos_coe, dist_comm p₁ p₃,
    cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
#align euclidean_geometry.cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two EuclideanGeometry.cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.sin (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ Real.Angle.sin (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
#align euclidean_geometry.sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two EuclideanGeometry.sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.sin (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₃ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ Real.Angle.sin (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₃ p₂
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.sin_coe, dist_comm p₁ p₃,
    sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]
#align euclidean_geometry.sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two EuclideanGeometry.sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.tan (∡ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ Real.Angle.tan (∡ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (right_ne_of_oangle_eq_pi_div_two h))]
#align euclidean_geometry.tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two EuclideanGeometry.tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.tan (∡ p₃ p₁ p₂) * dist p₁ p₂ = dist p₃ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ Real.Angle.tan (∡ p₃ p₁ p₂) * dist p₁ p₂ = dist p₃ p₂
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.tan_coe,
    tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h))]
#align euclidean_geometry.tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two EuclideanGeometry.tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem dist_div_cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.cos (∡ p₂ p₃ p₁) = dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ dist p₃ p₂ / Real.Angle.cos (∡ p₂ p₃ p₁) = dist p₁ p₃
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    dist_div_cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (right_ne_of_oangle_eq_pi_div_two h))]
#align euclidean_geometry.dist_div_cos_oangle_right_of_oangle_eq_pi_div_two EuclideanGeometry.dist_div_cos_oangle_right_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem dist_div_cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ dist p₁ p₂ / Real.Angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₃
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.cos_coe, dist_comm p₁ p₃,
    dist_div_cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h))]
#align euclidean_geometry.dist_div_cos_oangle_left_of_oangle_eq_pi_div_two EuclideanGeometry.dist_div_cos_oangle_left_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem dist_div_sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ dist p₁ p₂ / Real.Angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₃
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    dist_div_sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]
#align euclidean_geometry.dist_div_sin_oangle_right_of_oangle_eq_pi_div_two EuclideanGeometry.dist_div_sin_oangle_right_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem dist_div_sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.sin (∡ p₃ p₁ p₂) = dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ dist p₃ p₂ / Real.Angle.sin (∡ p₃ p₁ p₂) = dist p₁ p₃
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.sin_coe, dist_comm p₁ p₃,
    dist_div_sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (right_ne_of_oangle_eq_pi_div_two h))]
#align euclidean_geometry.dist_div_sin_oangle_left_of_oangle_eq_pi_div_two EuclideanGeometry.dist_div_sin_oangle_left_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem dist_div_tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.tan (∡ p₂ p₃ p₁) = dist p₃ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ dist p₁ p₂ / Real.Angle.tan (∡ p₂ p₃ p₁) = dist p₃ p₂
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    dist_div_tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]
#align euclidean_geometry.dist_div_tan_oangle_right_of_oangle_eq_pi_div_two EuclideanGeometry.dist_div_tan_oangle_right_of_oangle_eq_pi_div_two

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem dist_div_tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.tan (∡ p₃ p₁ p₂) = dist p₁ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  -- ⊢ dist p₃ p₂ / Real.Angle.tan (∡ p₃ p₁ p₂) = dist p₁ p₂
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.tan_coe,
    dist_div_tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (right_ne_of_oangle_eq_pi_div_two h))]
#align euclidean_geometry.dist_div_tan_oangle_left_of_oangle_eq_pi_div_two EuclideanGeometry.dist_div_tan_oangle_left_of_oangle_eq_pi_div_two

end EuclideanGeometry
