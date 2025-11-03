/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-!
# Oriented angles in right-angled triangles.

This file proves basic geometric results about distances and oriented angles in (possibly
degenerate) right-angled triangles in real inner product spaces and Euclidean affine spaces.

-/


noncomputable section

open scoped EuclideanGeometry

open scoped Real

open scoped RealInnerProductSpace

namespace Orientation

open Module

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

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_add_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arccos (‖y‖ / ‖x + y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arccos_of_oangle_eq_pi_div_two h

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arcsin (‖y‖ / ‖x + y‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_add_eq_arcsin_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_add_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arcsin (‖x‖ / ‖x + y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arcsin_of_oangle_eq_pi_div_two h

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle x (x + y) = Real.arctan (‖y‖ / ‖x‖) := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_add_eq_arctan_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h) (o.left_ne_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_add_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x + y) y = Real.arctan (‖x‖ / ‖y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two h

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle x (x + y)) = ‖x‖ / ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x + y) y) = ‖y‖ / ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).cos_oangle_add_right_of_oangle_eq_pi_div_two h

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle x (x + y)) = ‖y‖ / ‖x + y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.left_ne_zero_of_oangle_eq_pi_div_two h))]

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle (x + y) y) = ‖x‖ / ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).sin_oangle_add_right_of_oangle_eq_pi_div_two h

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_oangle_add_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle x (x + y)) = ‖y‖ / ‖x‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.tan_angle_add_of_inner_eq_zero (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle (x + y) y) = ‖x‖ / ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).tan_oangle_add_right_of_oangle_eq_pi_div_two h

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle x (x + y)) * ‖x + y‖ = ‖x‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle (x + y) y) * ‖x + y‖ = ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).cos_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle x (x + y)) * ‖x + y‖ = ‖y‖ := by
  have hs : (o.oangle x (x + y)).sign = 1 := by
    rw [oangle_sign_add_right, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_add_mul_norm_of_inner_eq_zero
      (o.inner_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle (x + y) y) * ‖x + y‖ = ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).sin_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

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

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_oangle_add_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle (x + y) y) * ‖y‖ = ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).tan_oangle_add_right_mul_norm_of_oangle_eq_pi_div_two h

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

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem norm_div_cos_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.cos (o.oangle (x + y) y) = ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_cos_oangle_add_right_of_oangle_eq_pi_div_two h

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

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem norm_div_sin_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.sin (o.oangle (x + y) y) = ‖x + y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_sin_oangle_add_right_of_oangle_eq_pi_div_two h

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

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem norm_div_tan_oangle_add_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.tan (o.oangle (x + y) y) = ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  rw [add_comm]
  exact (-o).norm_div_tan_oangle_add_right_of_oangle_eq_pi_div_two h

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
theorem oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arccos (‖y‖ / ‖y - x‖) := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_sub_eq_arccos_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arccos`, version subtracting vectors. -/
theorem oangle_sub_left_eq_arccos_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arccos (‖x‖ / ‖x - y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arccos_of_oangle_eq_pi_div_two h

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
theorem oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arcsin (‖x‖ / ‖y - x‖) := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_sub_eq_arcsin_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)
      (Or.inl (o.right_ne_zero_of_oangle_eq_pi_div_two h))]

/-- An angle in a right-angled triangle expressed using `arcsin`, version subtracting vectors. -/
theorem oangle_sub_left_eq_arcsin_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arcsin (‖y‖ / ‖x - y‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arcsin_of_oangle_eq_pi_div_two h

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
theorem oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle y (y - x) = Real.arctan (‖x‖ / ‖y‖) := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs,
    InnerProductGeometry.angle_sub_eq_arctan_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h) (o.right_ne_zero_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arctan`, version subtracting vectors. -/
theorem oangle_sub_left_eq_arctan_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    o.oangle (x - y) x = Real.arctan (‖y‖ / ‖x‖) := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).oangle_sub_right_eq_arctan_of_oangle_eq_pi_div_two h

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem cos_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle y (y - x)) = ‖y‖ / ‖y - x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.cos (o.oangle (x - y) x) = ‖x‖ / ‖x - y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).cos_oangle_sub_right_of_oangle_eq_pi_div_two h

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

/-- The sine of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.sin (o.oangle (x - y) x) = ‖y‖ / ‖x - y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).sin_oangle_sub_right_of_oangle_eq_pi_div_two h

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem tan_oangle_sub_right_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle y (y - x)) = ‖x‖ / ‖y‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    InnerProductGeometry.tan_angle_sub_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The tangent of an angle in a right-angled triangle as a ratio of sides, version subtracting
vectors. -/
theorem tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V} (h : o.oangle x y = ↑(π / 2)) :
    Real.Angle.tan (o.oangle (x - y) x) = ‖y‖ / ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).tan_oangle_sub_right_of_oangle_eq_pi_div_two h

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
theorem cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle y (y - x)) * ‖y - x‖ = ‖y‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    InnerProductGeometry.cos_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side, version subtracting vectors. -/
theorem cos_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.cos (o.oangle (x - y) x) * ‖x - y‖ = ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).cos_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
theorem sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle y (y - x)) * ‖y - x‖ = ‖x‖ := by
  have hs : (o.oangle y (y - x)).sign = 1 := by
    rw [oangle_sign_sub_right_swap, h, Real.Angle.sign_coe_pi_div_two]
  rw [o.oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    InnerProductGeometry.sin_angle_sub_mul_norm_of_inner_eq_zero
      (o.inner_rev_eq_zero_of_oangle_eq_pi_div_two h)]

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side, version subtracting vectors. -/
theorem sin_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.sin (o.oangle (x - y) x) * ‖x - y‖ = ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).sin_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

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

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side, version subtracting vectors. -/
theorem tan_oangle_sub_left_mul_norm_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : Real.Angle.tan (o.oangle (x - y) x) * ‖x‖ = ‖y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).tan_oangle_sub_right_mul_norm_of_oangle_eq_pi_div_two h

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

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse, version subtracting vectors. -/
theorem norm_div_cos_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖x‖ / Real.Angle.cos (o.oangle (x - y) x) = ‖x - y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).norm_div_cos_oangle_sub_right_of_oangle_eq_pi_div_two h

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

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse, version subtracting vectors. -/
theorem norm_div_sin_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.sin (o.oangle (x - y) x) = ‖x - y‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).norm_div_sin_oangle_sub_right_of_oangle_eq_pi_div_two h

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

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side, version subtracting vectors. -/
theorem norm_div_tan_oangle_sub_left_of_oangle_eq_pi_div_two {x y : V}
    (h : o.oangle x y = ↑(π / 2)) : ‖y‖ / Real.Angle.tan (o.oangle (x - y) x) = ‖x‖ := by
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj] at h ⊢
  exact (-o).norm_div_tan_oangle_sub_right_of_oangle_eq_pi_div_two h

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
    rw [← neg_inj, ← oangle_neg_orientation_eq_neg, neg_neg] at ha
    rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj, oangle_rev,
      (-o).oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two ha, norm_smul,
      LinearIsometryEquiv.norm_map, mul_div_assoc, div_self (norm_ne_zero_iff.2 h), mul_one,
      Real.norm_eq_abs, abs_of_neg hr, Real.arctan_neg, Real.Angle.coe_neg, neg_neg]
  · rw [zero_smul, add_zero, oangle_self, Real.arctan_zero, Real.Angle.coe_zero]
  · have ha : o.oangle x (r • o.rotation (π / 2 : ℝ) x) = (π / 2 : ℝ) := by
      rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right h]
    rw [o.oangle_add_right_eq_arctan_of_oangle_eq_pi_div_two ha, norm_smul,
      LinearIsometryEquiv.norm_map, mul_div_assoc, div_self (norm_ne_zero_iff.2 h), mul_one,
      Real.norm_eq_abs, abs_of_pos hr]

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`. -/
theorem oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle (x + r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x)
      = Real.arctan r⁻¹ := by
  by_cases hr : r = 0; · simp [hr]
  rw [← neg_inj, oangle_rev, ← oangle_neg_orientation_eq_neg, neg_inj, ←
    neg_neg ((π / 2 : ℝ) : Real.Angle), ← rotation_neg_orientation_eq_neg, add_comm]
  have hx : x = r⁻¹ • (-o).rotation (π / 2 : ℝ) (r • (-o).rotation (-(π / 2 : ℝ)) x) := by simp [hr]
  nth_rw 3 [hx]
  refine (-o).oangle_add_right_smul_rotation_pi_div_two ?_ _
  simp [hr, h]

/-- The tangent of an angle in a right-angled triangle, where one side is a multiple of a
rotation of another by `π / 2`. -/
theorem tan_oangle_add_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    Real.Angle.tan (o.oangle x (x + r • o.rotation (π / 2 : ℝ) x)) = r := by
  rw [o.oangle_add_right_smul_rotation_pi_div_two h, Real.Angle.tan_coe, Real.tan_arctan]

/-- The tangent of an angle in a right-angled triangle, where one side is a multiple of a
rotation of another by `π / 2`. -/
theorem tan_oangle_add_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    Real.Angle.tan (o.oangle (x + r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x)) =
      r⁻¹ := by
  rw [o.oangle_add_left_smul_rotation_pi_div_two h, Real.Angle.tan_coe, Real.tan_arctan]

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`, version subtracting vectors. -/
theorem oangle_sub_right_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle (r • o.rotation (π / 2 : ℝ) x) (r • o.rotation (π / 2 : ℝ) x - x)
      = Real.arctan r⁻¹ := by
  by_cases hr : r = 0; · simp [hr]
  have hx : -x = r⁻¹ • o.rotation (π / 2 : ℝ) (r • o.rotation (π / 2 : ℝ) x) := by
    simp [hr, ← Real.Angle.coe_add]
  rw [sub_eq_add_neg, hx, o.oangle_add_right_smul_rotation_pi_div_two]
  simpa [hr] using h

/-- An angle in a right-angled triangle expressed using `arctan`, where one side is a multiple
of a rotation of another by `π / 2`, version subtracting vectors. -/
theorem oangle_sub_left_smul_rotation_pi_div_two {x : V} (h : x ≠ 0) (r : ℝ) :
    o.oangle (x - r • o.rotation (π / 2 : ℝ) x) x = Real.arctan r := by
  by_cases hr : r = 0; · simp [hr]
  have hx : x = r⁻¹ • o.rotation (π / 2 : ℝ) (-(r • o.rotation (π / 2 : ℝ) x)) := by
    simp [hr, ← Real.Angle.coe_add]
  rw [sub_eq_add_neg, add_comm]
  nth_rw 3 [hx]
  nth_rw 2 [hx]
  rw [o.oangle_add_left_smul_rotation_pi_div_two, inv_inv]
  simpa [hr] using h

end Orientation

namespace EuclideanGeometry

open Module

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_right_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arccos (dist p₃ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs,
    angle_eq_arccos_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arccos`. -/
theorem oangle_left_eq_arccos_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arccos (dist p₁ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm,
    angle_eq_arccos_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h),
    dist_comm p₁ p₃]

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_right_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arcsin (dist p₁ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs,
    angle_eq_arcsin_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

/-- An angle in a right-angled triangle expressed using `arcsin`. -/
theorem oangle_left_eq_arcsin_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arcsin (dist p₃ p₂ / dist p₁ p₃) := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm,
    angle_eq_arcsin_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h)),
    dist_comm p₁ p₃]

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_right_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₂ p₃ p₁ = Real.arctan (dist p₁ p₂ / dist p₃ p₂) := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs,
    angle_eq_arctan_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (right_ne_of_oangle_eq_pi_div_two h)]

/-- An angle in a right-angled triangle expressed using `arctan`. -/
theorem oangle_left_eq_arctan_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    ∡ p₃ p₁ p₂ = Real.arctan (dist p₃ p₂ / dist p₁ p₂) := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm,
    angle_eq_arctan_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (left_ne_of_oangle_eq_pi_div_two h)]

/-- An oriented angle in a right-angled triangle (even a degenerate one) has absolute value less
than `π / 2`. The right-angled property is expressed using unoriented angles to cover either
orientation of right-angled triangles and include degenerate cases. -/
lemma abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∠ p₁ p₂ p₃ = π / 2) : |(∡ p₂ p₃ p₁).toReal| < π / 2 := by
  by_cases hp₂ : p₂ = p₃
  · simp [hp₂, Real.pi_pos]
  by_cases hp₁ : p₁ = p₃
  · simp [hp₁, Real.pi_pos]
  rw [← angle_eq_abs_oangle_toReal hp₂ hp₁]
  exact angle_lt_pi_div_two_of_angle_eq_pi_div_two h (Ne.symm hp₂)

/-- Two oriented angles in right-angled triangles are equal if twice those angles are equal. -/
lemma oangle_eq_oangle_of_two_zsmul_eq_of_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : ℤ) • ∡ p₂ p₃ p₁ = (2 : ℤ) • ∡ p₅ p₆ p₄) (h₁₂₃ : ∠ p₁ p₂ p₃ = π / 2)
    (h₄₅₆ : ∠ p₄ p₅ p₆ = π / 2) : ∡ p₂ p₃ p₁ = ∡ p₅ p₆ p₄ := by
  rwa [Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₁₂₃)
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₄₅₆)] at h

/-- Two oriented angles in oppositely-oriented right-angled triangles are equal if twice those
angles are equal. -/
lemma oangle_eq_oangle_rev_of_two_zsmul_eq_of_angle_eq_pi_div_two {p₁ p₂ p₃ p₄ p₅ p₆ : P}
    (h : (2 : ℤ) • ∡ p₂ p₃ p₁ = (2 : ℤ) • ∡ p₄ p₆ p₅) (h₁₂₃ : ∠ p₁ p₂ p₃ = π / 2)
    (h₄₅₆ : ∠ p₄ p₅ p₆ = π / 2) : ∡ p₂ p₃ p₁ = ∡ p₄ p₆ p₅ := by
  refine (Real.Angle.two_zsmul_eq_iff_eq_of_abs_toReal_lt_pi_div_two
    (abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₁₂₃) ?_).1 h
  rw [oangle_rev]
  suffices |(∡ p₅ p₆ p₄).toReal| < π / 2 by
    convert this using 1
    nth_rw 2 [← abs_neg]
    congr
    rw [Real.Angle.toReal_neg_eq_neg_toReal_iff]
    intro hc
    simp only [hc, Real.Angle.toReal_pi, abs_of_pos Real.pi_pos] at this
    linarith [Real.pi_pos]
  exact abs_oangle_toReal_lt_pi_div_two_of_angle_eq_pi_div_two h₄₅₆

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.cos (∡ p₂ p₃ p₁) = dist p₃ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle as a ratio of sides. -/
theorem cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.cos_coe,
    cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h),
    dist_comm p₁ p₃]

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

/-- The sine of an angle in a right-angled triangle as a ratio of sides. -/
theorem sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.sin (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.sin_coe,
    sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h)),
    dist_comm p₁ p₃]

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.tan (∡ p₂ p₃ p₁) = dist p₁ p₂ / dist p₃ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The tangent of an angle in a right-angled triangle as a ratio of sides. -/
theorem tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P} (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) :
    Real.Angle.tan (∡ p₃ p₁ p₂) = dist p₃ p₂ / dist p₁ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.tan_coe,
    tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.cos (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₃ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The cosine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
adjacent side. -/
theorem cos_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.cos (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₁ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.cos_coe, dist_comm p₁ p₃,
    cos_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.sin (∡ p₂ p₃ p₁) * dist p₁ p₃ = dist p₁ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The sine of an angle in a right-angled triangle multiplied by the hypotenuse equals the
opposite side. -/
theorem sin_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.sin (∡ p₃ p₁ p₂) * dist p₁ p₃ = dist p₃ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.sin_coe, dist_comm p₁ p₃,
    sin_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)]

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_oangle_right_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.tan (∡ p₂ p₃ p₁) * dist p₃ p₂ = dist p₁ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (right_ne_of_oangle_eq_pi_div_two h))]

/-- The tangent of an angle in a right-angled triangle multiplied by the adjacent side equals
the opposite side. -/
theorem tan_oangle_left_mul_dist_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : Real.Angle.tan (∡ p₃ p₁ p₂) * dist p₁ p₂ = dist p₃ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.tan_coe,
    tan_angle_mul_dist_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem dist_div_cos_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.cos (∡ p₂ p₃ p₁) = dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.cos_coe,
    dist_div_cos_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (right_ne_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the cosine of the adjacent angle equals the
hypotenuse. -/
theorem dist_div_cos_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.cos (∡ p₃ p₁ p₂) = dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.cos_coe, dist_comm p₁ p₃,
    dist_div_cos_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inr (left_ne_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem dist_div_sin_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.sin (∡ p₂ p₃ p₁) = dist p₁ p₃ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.sin_coe,
    dist_div_sin_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the sine of the opposite angle equals the
hypotenuse. -/
theorem dist_div_sin_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.sin (∡ p₃ p₁ p₂) = dist p₁ p₃ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.sin_coe, dist_comm p₁ p₃,
    dist_div_sin_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (right_ne_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem dist_div_tan_oangle_right_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₁ p₂ / Real.Angle.tan (∡ p₂ p₃ p₁) = dist p₃ p₂ := by
  have hs : (∡ p₂ p₃ p₁).sign = 1 := by rw [oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, Real.Angle.tan_coe,
    dist_div_tan_angle_of_angle_eq_pi_div_two (angle_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (left_ne_of_oangle_eq_pi_div_two h))]

/-- A side of a right-angled triangle divided by the tangent of the opposite angle equals the
adjacent side. -/
theorem dist_div_tan_oangle_left_of_oangle_eq_pi_div_two {p₁ p₂ p₃ : P}
    (h : ∡ p₁ p₂ p₃ = ↑(π / 2)) : dist p₃ p₂ / Real.Angle.tan (∡ p₃ p₁ p₂) = dist p₁ p₂ := by
  have hs : (∡ p₃ p₁ p₂).sign = 1 := by rw [← oangle_rotate_sign, h, Real.Angle.sign_coe_pi_div_two]
  rw [oangle_eq_angle_of_sign_eq_one hs, angle_comm, Real.Angle.tan_coe,
    dist_div_tan_angle_of_angle_eq_pi_div_two (angle_rev_eq_pi_div_two_of_oangle_eq_pi_div_two h)
      (Or.inl (right_ne_of_oangle_eq_pi_div_two h))]

end EuclideanGeometry
