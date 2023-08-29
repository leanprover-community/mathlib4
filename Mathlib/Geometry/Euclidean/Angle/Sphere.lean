/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Angle.Oriented.RightAngle
import Mathlib.Geometry.Euclidean.Circumcenter

#align_import geometry.euclidean.angle.sphere from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Angles in circles and sphere.

This file proves results about angles in circles and spheres.

-/


noncomputable section

open FiniteDimensional Complex

open scoped EuclideanGeometry Real RealInnerProductSpace ComplexConjugate

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable [Fact (finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form. -/
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
    (hxy : ‖x‖ = ‖y‖) (hxz : ‖x‖ = ‖z‖) : o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) := by
  have hy : y ≠ 0 := by
    rintro rfl
    rw [norm_zero, norm_eq_zero] at hxy
    exact hxyne hxy
  have hx : x ≠ 0 := norm_ne_zero_iff.1 (hxy.symm ▸ norm_ne_zero_iff.2 hy)
  -- ⊢ oangle o y z = 2 • oangle o (y - x) (z - x)
  have hz : z ≠ 0 := norm_ne_zero_iff.1 (hxz ▸ norm_ne_zero_iff.2 hx)
  -- ⊢ oangle o y z = 2 • oangle o (y - x) (z - x)
  calc
    o.oangle y z = o.oangle x z - o.oangle x y := (o.oangle_sub_left hx hy hz).symm
    _ = π - (2 : ℤ) • o.oangle (x - z) x - (π - (2 : ℤ) • o.oangle (x - y) x) := by
      rw [o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxzne.symm hxz.symm,
        o.oangle_eq_pi_sub_two_zsmul_oangle_sub_of_norm_eq hxyne.symm hxy.symm]
    _ = (2 : ℤ) • (o.oangle (x - y) x - o.oangle (x - z) x) := by abel
    _ = (2 : ℤ) • o.oangle (x - y) (x - z) := by
      rw [o.oangle_sub_right (sub_ne_zero_of_ne hxyne) (sub_ne_zero_of_ne hxzne) hx]
    _ = (2 : ℤ) • o.oangle (y - x) (z - x) := by rw [← oangle_neg_neg, neg_sub, neg_sub]
#align orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq Orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq

/-- Angle at center of a circle equals twice angle at circumference, oriented vector angle
form with radius specified. -/
theorem oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real {x y z : V} (hxyne : x ≠ y) (hxzne : x ≠ z)
    {r : ℝ} (hx : ‖x‖ = r) (hy : ‖y‖ = r) (hz : ‖z‖ = r) :
    o.oangle y z = (2 : ℤ) • o.oangle (y - x) (z - x) :=
  o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq hxyne hxzne (hy.symm ▸ hx) (hz.symm ▸ hx)
#align orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real Orientation.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real

/-- Oriented vector angle version of "angles in same segment are equal" and "opposite angles of
a cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same
result), represented here as equality of twice the angles. -/
theorem two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq {x₁ x₂ y z : V} (hx₁yne : x₁ ≠ y)
    (hx₁zne : x₁ ≠ z) (hx₂yne : x₂ ≠ y) (hx₂zne : x₂ ≠ z) {r : ℝ} (hx₁ : ‖x₁‖ = r) (hx₂ : ‖x₂‖ = r)
    (hy : ‖y‖ = r) (hz : ‖z‖ = r) :
    (2 : ℤ) • o.oangle (y - x₁) (z - x₁) = (2 : ℤ) • o.oangle (y - x₂) (z - x₂) :=
  o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₁yne hx₁zne hx₁ hy hz ▸
    o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real hx₂yne hx₂zne hx₂ hy hz
#align orientation.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq Orientation.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq

end Orientation

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

local notation "o" => Module.Oriented.positiveOrientation

namespace Sphere

/-- Angle at center of a circle equals twice angle at circumference, oriented angle version. -/
theorem oangle_center_eq_two_zsmul_oangle {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₃ : p₂ ≠ p₃) :
    ∡ p₁ s.center p₃ = (2 : ℤ) • ∡ p₁ p₂ p₃ := by
  rw [mem_sphere, @dist_eq_norm_vsub V] at hp₁ hp₂ hp₃
  -- ⊢ ∡ p₁ s.center p₃ = 2 • ∡ p₁ p₂ p₃
  rw [oangle, oangle, o.oangle_eq_two_zsmul_oangle_sub_of_norm_eq_real _ _ hp₂ hp₁ hp₃] <;>
    simp [hp₂p₁, hp₂p₃]
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
#align euclidean_geometry.sphere.oangle_center_eq_two_zsmul_oangle EuclideanGeometry.Sphere.oangle_center_eq_two_zsmul_oangle

/-- Oriented angle version of "angles in same segment are equal" and "opposite angles of a
cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same result),
represented here as equality of twice the angles. -/
theorem two_zsmul_oangle_eq {s : Sphere P} {p₁ p₂ p₃ p₄ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s)
    (hp₃ : p₃ ∈ s) (hp₄ : p₄ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₄ : p₂ ≠ p₄) (hp₃p₁ : p₃ ≠ p₁)
    (hp₃p₄ : p₃ ≠ p₄) : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄ := by
  rw [mem_sphere, @dist_eq_norm_vsub V] at hp₁ hp₂ hp₃ hp₄
  -- ⊢ 2 • ∡ p₁ p₂ p₄ = 2 • ∡ p₁ p₃ p₄
  rw [oangle, oangle, ← vsub_sub_vsub_cancel_right p₁ p₂ s.center, ←
      vsub_sub_vsub_cancel_right p₄ p₂ s.center,
      o.two_zsmul_oangle_sub_eq_two_zsmul_oangle_sub_of_norm_eq _ _ _ _ hp₂ hp₃ hp₁ hp₄] <;>
    simp [hp₂p₁, hp₂p₄, hp₃p₁, hp₃p₄]
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
#align euclidean_geometry.sphere.two_zsmul_oangle_eq EuclideanGeometry.Sphere.two_zsmul_oangle_eq

end Sphere

/-- Oriented angle version of "angles in same segment are equal" and "opposite angles of a
cyclic quadrilateral add to π", for oriented angles mod π (for which those are the same result),
represented here as equality of twice the angles. -/
theorem Cospherical.two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
    (h : Cospherical ({p₁, p₂, p₃, p₄} : Set P)) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₄ : p₂ ≠ p₄)
    (hp₃p₁ : p₃ ≠ p₁) (hp₃p₄ : p₃ ≠ p₄) : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄ := by
  obtain ⟨s, hs⟩ := cospherical_iff_exists_sphere.1 h
  -- ⊢ 2 • ∡ p₁ p₂ p₄ = 2 • ∡ p₁ p₃ p₄
  simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff, Sphere.mem_coe] at hs
  -- ⊢ 2 • ∡ p₁ p₂ p₄ = 2 • ∡ p₁ p₃ p₄
  exact Sphere.two_zsmul_oangle_eq hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hp₂p₁ hp₂p₄ hp₃p₁ hp₃p₄
  -- 🎉 no goals
#align euclidean_geometry.cospherical.two_zsmul_oangle_eq EuclideanGeometry.Cospherical.two_zsmul_oangle_eq

namespace Sphere

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
angle-at-point form where the apex is given as the center of a circle. -/
theorem oangle_eq_pi_sub_two_zsmul_oangle_center_left {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) : ∡ p₁ s.center p₂ = π - (2 : ℤ) • ∡ s.center p₂ p₁ := by
  rw [oangle_eq_pi_sub_two_zsmul_oangle_of_dist_eq h.symm
      (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]
#align euclidean_geometry.sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_left EuclideanGeometry.Sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_left

/-- The angle at the apex of an isosceles triangle is `π` minus twice a base angle, oriented
angle-at-point form where the apex is given as the center of a circle. -/
theorem oangle_eq_pi_sub_two_zsmul_oangle_center_right {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) : ∡ p₁ s.center p₂ = π - (2 : ℤ) • ∡ p₂ p₁ s.center := by
  rw [oangle_eq_pi_sub_two_zsmul_oangle_center_left hp₁ hp₂ h,
    oangle_eq_oangle_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)]
#align euclidean_geometry.sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_right EuclideanGeometry.Sphere.oangle_eq_pi_sub_two_zsmul_oangle_center_right

/-- Twice a base angle of an isosceles triangle with apex at the center of a circle, plus twice
the angle at the apex of a triangle with the same base but apex on the circle, equals `π`. -/
theorem two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi {s : Sphere P} {p₁ p₂ p₃ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₂p₁ : p₂ ≠ p₁) (hp₂p₃ : p₂ ≠ p₃)
    (hp₁p₃ : p₁ ≠ p₃) : (2 : ℤ) • ∡ p₃ p₁ s.center + (2 : ℤ) • ∡ p₁ p₂ p₃ = π := by
  rw [← oangle_center_eq_two_zsmul_oangle hp₁ hp₂ hp₃ hp₂p₁ hp₂p₃,
    oangle_eq_pi_sub_two_zsmul_oangle_center_right hp₁ hp₃ hp₁p₃, add_sub_cancel'_right]
#align euclidean_geometry.sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi EuclideanGeometry.Sphere.two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi

/-- A base angle of an isosceles triangle with apex at the center of a circle is acute. -/
theorem abs_oangle_center_left_toReal_lt_pi_div_two {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : |(∡ s.center p₂ p₁).toReal| < π / 2 :=
  abs_oangle_right_toReal_lt_pi_div_two_of_dist_eq
    (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)
#align euclidean_geometry.sphere.abs_oangle_center_left_to_real_lt_pi_div_two EuclideanGeometry.Sphere.abs_oangle_center_left_toReal_lt_pi_div_two

/-- A base angle of an isosceles triangle with apex at the center of a circle is acute. -/
theorem abs_oangle_center_right_toReal_lt_pi_div_two {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : |(∡ p₂ p₁ s.center).toReal| < π / 2 :=
  abs_oangle_left_toReal_lt_pi_div_two_of_dist_eq
    (dist_center_eq_dist_center_of_mem_sphere' hp₂ hp₁)
#align euclidean_geometry.sphere.abs_oangle_center_right_to_real_lt_pi_div_two EuclideanGeometry.Sphere.abs_oangle_center_right_toReal_lt_pi_div_two

/-- Given two points on a circle, the center of that circle may be expressed explicitly as a
multiple (by half the tangent of the angle between the chord and the radius at one of those
points) of a `π / 2` rotation of the vector between those points, plus the midpoint of those
points. -/
theorem tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center {s : Sphere P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) :
    (Real.Angle.tan (∡ p₂ p₁ s.center) / 2) • o.rotation (π / 2 : ℝ) (p₂ -ᵥ p₁) +ᵥ
      midpoint ℝ p₁ p₂ = s.center := by
  obtain ⟨r, hr⟩ := (dist_eq_iff_eq_smul_rotation_pi_div_two_vadd_midpoint h).1
    (dist_center_eq_dist_center_of_mem_sphere hp₁ hp₂)
  rw [← hr, ← oangle_midpoint_rev_left, oangle, vadd_vsub_assoc]
  -- ⊢ (Real.Angle.tan (Orientation.oangle o (midpoint ℝ p₁ p₂ -ᵥ p₁) (r • ↑(Orient …
  nth_rw 1 [show p₂ -ᵥ p₁ = (2 : ℝ) • (midpoint ℝ p₁ p₂ -ᵥ p₁) by simp]
  -- ⊢ (Real.Angle.tan (Orientation.oangle o (midpoint ℝ p₁ p₂ -ᵥ p₁) (r • ↑(Orient …
  rw [map_smul, smul_smul, add_comm, o.tan_oangle_add_right_smul_rotation_pi_div_two,
    mul_div_cancel _ (two_ne_zero' ℝ)]
  simpa using h.symm
  -- 🎉 no goals
#align euclidean_geometry.sphere.tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center EuclideanGeometry.Sphere.tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center

/-- Given three points on a circle, the center of that circle may be expressed explicitly as a
multiple (by half the inverse of the tangent of the angle at one of those points) of a `π / 2`
rotation of the vector between the other two points, plus the midpoint of those points. -/
theorem inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center {s : Sphere P}
    {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃)
    (hp₂p₃ : p₂ ≠ p₃) :
    ((Real.Angle.tan (∡ p₁ p₂ p₃))⁻¹ / 2) • o.rotation (π / 2 : ℝ) (p₃ -ᵥ p₁) +ᵥ midpoint ℝ p₁ p₃ =
      s.center := by
  convert tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₃ hp₁p₃
  -- ⊢ (Real.Angle.tan (∡ p₁ p₂ p₃))⁻¹ = Real.Angle.tan (∡ p₃ p₁ s.center)
  convert (Real.Angle.tan_eq_inv_of_two_zsmul_add_two_zsmul_eq_pi _).symm
  -- ⊢ 2 • ∡ p₁ p₂ p₃ + 2 • ∡ p₃ p₁ s.center = ↑π
  rw [add_comm,
    two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃]
#align euclidean_geometry.sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center EuclideanGeometry.Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center

/-- Given two points on a circle, the radius of that circle may be expressed explicitly as half
the distance between those two points divided by the cosine of the angle between the chord and
the radius at one of those points. -/
theorem dist_div_cos_oangle_center_div_two_eq_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) :
    dist p₁ p₂ / Real.Angle.cos (∡ p₂ p₁ s.center) / 2 = s.radius := by
  rw [div_right_comm, div_eq_mul_inv _ (2 : ℝ), mul_comm,
    show (2 : ℝ)⁻¹ * dist p₁ p₂ = dist p₁ (midpoint ℝ p₁ p₂) by simp, ← mem_sphere.1 hp₁, ←
    tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center hp₁ hp₂ h, ←
    oangle_midpoint_rev_left, oangle, vadd_vsub_assoc,
    show p₂ -ᵥ p₁ = (2 : ℝ) • (midpoint ℝ p₁ p₂ -ᵥ p₁) by simp, map_smul, smul_smul,
    div_mul_cancel _ (two_ne_zero' ℝ), @dist_eq_norm_vsub' V, @dist_eq_norm_vsub' V,
    vadd_vsub_assoc, add_comm, o.oangle_add_right_smul_rotation_pi_div_two, Real.Angle.cos_coe,
    Real.cos_arctan]
  norm_cast
  -- ⊢ ‖midpoint ℝ p₁ p₂ -ᵥ p₁‖ / (1 / Real.sqrt (1 + Real.Angle.tan (∡ p₂ p₁ s.cen …
  rw [one_div, div_inv_eq_mul, ←
    mul_self_inj (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (norm_nonneg _),
    norm_add_sq_eq_norm_sq_add_norm_sq_real (o.inner_smul_rotation_pi_div_two_right _ _), ←
    mul_assoc, mul_comm, mul_comm _ (Real.sqrt _), ← mul_assoc, ← mul_assoc,
    Real.mul_self_sqrt (add_nonneg zero_le_one (sq_nonneg _)), norm_smul,
    LinearIsometryEquiv.norm_map]
  swap; · simpa using h.symm
  -- ⊢ midpoint ℝ p₁ p₂ -ᵥ p₁ ≠ 0
          -- 🎉 no goals
  conv_rhs =>
    rw [← mul_assoc, mul_comm _ ‖Real.Angle.tan _‖, ← mul_assoc, Real.norm_eq_abs, abs_mul_abs_self]
  ring
  -- 🎉 no goals
#align euclidean_geometry.sphere.dist_div_cos_oangle_center_div_two_eq_radius EuclideanGeometry.Sphere.dist_div_cos_oangle_center_div_two_eq_radius

/-- Given two points on a circle, twice the radius of that circle may be expressed explicitly as
the distance between those two points divided by the cosine of the angle between the chord and
the radius at one of those points. -/
theorem dist_div_cos_oangle_center_eq_two_mul_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (h : p₁ ≠ p₂) :
    dist p₁ p₂ / Real.Angle.cos (∡ p₂ p₁ s.center) = 2 * s.radius := by
  rw [← dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₂ h, mul_div_cancel' _ (two_ne_zero' ℝ)]
  -- 🎉 no goals
#align euclidean_geometry.sphere.dist_div_cos_oangle_center_eq_two_mul_radius EuclideanGeometry.Sphere.dist_div_cos_oangle_center_eq_two_mul_radius

/-- Given three points on a circle, the radius of that circle may be expressed explicitly as half
the distance between two of those points divided by the absolute value of the sine of the angle
at the third point (a version of the law of sines or sine rule). -/
theorem dist_div_sin_oangle_div_two_eq_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| / 2 = s.radius := by
  convert dist_div_cos_oangle_center_div_two_eq_radius hp₁ hp₃ hp₁p₃
  -- ⊢ |Real.Angle.sin (∡ p₁ p₂ p₃)| = Real.Angle.cos (∡ p₃ p₁ s.center)
  rw [← Real.Angle.abs_cos_eq_abs_sin_of_two_zsmul_add_two_zsmul_eq_pi
    (two_zsmul_oangle_center_add_two_zsmul_oangle_eq_pi hp₁ hp₂ hp₃ hp₁p₂.symm hp₂p₃ hp₁p₃),
    _root_.abs_of_nonneg (Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two.2 _)]
  exact (abs_oangle_center_right_toReal_lt_pi_div_two hp₁ hp₃).le
  -- 🎉 no goals
#align euclidean_geometry.sphere.dist_div_sin_oangle_div_two_eq_radius EuclideanGeometry.Sphere.dist_div_sin_oangle_div_two_eq_radius

/-- Given three points on a circle, twice the radius of that circle may be expressed explicitly as
the distance between two of those points divided by the absolute value of the sine of the angle
at the third point (a version of the law of sines or sine rule). -/
theorem dist_div_sin_oangle_eq_two_mul_radius {s : Sphere P} {p₁ p₂ p₃ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) (hp₁p₂ : p₁ ≠ p₂) (hp₁p₃ : p₁ ≠ p₃) (hp₂p₃ : p₂ ≠ p₃) :
    dist p₁ p₃ / |Real.Angle.sin (∡ p₁ p₂ p₃)| = 2 * s.radius := by
  rw [← dist_div_sin_oangle_div_two_eq_radius hp₁ hp₂ hp₃ hp₁p₂ hp₁p₃ hp₂p₃,
    mul_div_cancel' _ (two_ne_zero' ℝ)]
#align euclidean_geometry.sphere.dist_div_sin_oangle_eq_two_mul_radius EuclideanGeometry.Sphere.dist_div_sin_oangle_eq_two_mul_radius

end Sphere

end EuclideanGeometry

namespace Affine

namespace Triangle

open EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

local notation "o" => Module.Oriented.positiveOrientation

/-- The circumcenter of a triangle may be expressed explicitly as a multiple (by half the inverse
of the tangent of the angle at one of the vertices) of a `π / 2` rotation of the vector between
the other two vertices, plus the midpoint of those vertices. -/
theorem inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter (t : Triangle ℝ P)
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    ((Real.Angle.tan (∡ (t.points i₁) (t.points i₂) (t.points i₃)))⁻¹ / 2) •
      o.rotation (π / 2 : ℝ) (t.points i₃ -ᵥ t.points i₁) +ᵥ
        midpoint ℝ (t.points i₁) (t.points i₃) = t.circumcenter :=
  Sphere.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_center (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.mem_circumsphere _) (t.Independent.injective.ne h₁₂)
    (t.Independent.injective.ne h₁₃) (t.Independent.injective.ne h₂₃)
#align affine.triangle.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter Affine.Triangle.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter

/-- The circumradius of a triangle may be expressed explicitly as half the length of a side
divided by the absolute value of the sine of the angle at the third point (a version of the law
of sines or sine rule). -/
theorem dist_div_sin_oangle_div_two_eq_circumradius (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) : dist (t.points i₁) (t.points i₃) /
      |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| / 2 = t.circumradius :=
  Sphere.dist_div_sin_oangle_div_two_eq_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.Independent.injective.ne h₁₂) (t.Independent.injective.ne h₁₃)
    (t.Independent.injective.ne h₂₃)
#align affine.triangle.dist_div_sin_oangle_div_two_eq_circumradius Affine.Triangle.dist_div_sin_oangle_div_two_eq_circumradius

/-- Twice the circumradius of a triangle may be expressed explicitly as the length of a side
divided by the absolute value of the sine of the angle at the third point (a version of the law
of sines or sine rule). -/
theorem dist_div_sin_oangle_eq_two_mul_circumradius (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) : dist (t.points i₁) (t.points i₃) /
      |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| = 2 * t.circumradius :=
  Sphere.dist_div_sin_oangle_eq_two_mul_radius (t.mem_circumsphere _) (t.mem_circumsphere _)
    (t.mem_circumsphere _) (t.Independent.injective.ne h₁₂) (t.Independent.injective.ne h₁₃)
    (t.Independent.injective.ne h₂₃)
#align affine.triangle.dist_div_sin_oangle_eq_two_mul_circumradius Affine.Triangle.dist_div_sin_oangle_eq_two_mul_circumradius

/-- The circumsphere of a triangle may be expressed explicitly in terms of two points and the
angle at the third point. -/
theorem circumsphere_eq_of_dist_of_oangle (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) : t.circumsphere =
    ⟨((Real.Angle.tan (∡ (t.points i₁) (t.points i₂) (t.points i₃)))⁻¹ / 2) •
      o.rotation (π / 2 : ℝ) (t.points i₃ -ᵥ t.points i₁) +ᵥ midpoint ℝ (t.points i₁) (t.points i₃),
      dist (t.points i₁) (t.points i₃) /
        |Real.Angle.sin (∡ (t.points i₁) (t.points i₂) (t.points i₃))| / 2⟩ :=
  t.circumsphere.ext _
    (t.inv_tan_div_two_smul_rotation_pi_div_two_vadd_midpoint_eq_circumcenter h₁₂ h₁₃ h₂₃).symm
    (t.dist_div_sin_oangle_div_two_eq_circumradius h₁₂ h₁₃ h₂₃).symm
#align affine.triangle.circumsphere_eq_of_dist_of_oangle Affine.Triangle.circumsphere_eq_of_dist_of_oangle

/-- If two triangles have two points the same, and twice the angle at the third point the same,
they have the same circumsphere. -/
theorem circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq {t₁ t₂ : Triangle ℝ P}
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (h₁ : t₁.points i₁ = t₂.points i₁) (h₃ : t₁.points i₃ = t₂.points i₃)
    (h₂ : (2 : ℤ) • ∡ (t₁.points i₁) (t₁.points i₂) (t₁.points i₃) =
      (2 : ℤ) • ∡ (t₂.points i₁) (t₂.points i₂) (t₂.points i₃)) :
    t₁.circumsphere = t₂.circumsphere := by
  rw [t₁.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃,
    t₂.circumsphere_eq_of_dist_of_oangle h₁₂ h₁₃ h₂₃,
    -- Porting note: was `congrm ⟨((_ : ℝ)⁻¹ / 2) • _ +ᵥ _, _ / _ / 2⟩` and five more lines
    Real.Angle.tan_eq_of_two_zsmul_eq h₂, Real.Angle.abs_sin_eq_of_two_zsmul_eq h₂, h₁, h₃]
#align affine.triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq Affine.Triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq

/-- Given a triangle, and a fourth point such that twice the angle between two points of the
triangle at that fourth point equals twice the third angle of the triangle, the fourth point
lies in the circumsphere of the triangle. -/
theorem mem_circumsphere_of_two_zsmul_oangle_eq {t : Triangle ℝ P} {p : P} {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (h : (2 : ℤ) • ∡ (t.points i₁) p (t.points i₃) =
      (2 : ℤ) • ∡ (t.points i₁) (t.points i₂) (t.points i₃)) : p ∈ t.circumsphere := by
  let t'p : Fin 3 → P := Function.update t.points i₂ p
  -- ⊢ p ∈ Simplex.circumsphere t
  have h₁ : t'p i₁ = t.points i₁ := by simp [h₁₂]
  -- ⊢ p ∈ Simplex.circumsphere t
  have h₂ : t'p i₂ = p := by simp
  -- ⊢ p ∈ Simplex.circumsphere t
  have h₃ : t'p i₃ = t.points i₃ := by simp [h₂₃.symm]
  -- ⊢ p ∈ Simplex.circumsphere t
  have ha : AffineIndependent ℝ t'p := by
    rw [affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃, h₁, h₂, h₃,
      collinear_iff_of_two_zsmul_oangle_eq h, ←
      affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃]
    exact t.Independent
  let t' : Triangle ℝ P := ⟨t'p, ha⟩
  -- ⊢ p ∈ Simplex.circumsphere t
  have h₁' : t'.points i₁ = t.points i₁ := h₁
  -- ⊢ p ∈ Simplex.circumsphere t
  have h₂' : t'.points i₂ = p := h₂
  -- ⊢ p ∈ Simplex.circumsphere t
  have h₃' : t'.points i₃ = t.points i₃ := h₃
  -- ⊢ p ∈ Simplex.circumsphere t
  have h' : (2 : ℤ) • ∡ (t'.points i₁) (t'.points i₂) (t'.points i₃) =
      (2 : ℤ) • ∡ (t.points i₁) (t.points i₂) (t.points i₃) := by rwa [h₁', h₂', h₃']
  rw [← circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ h₁' h₃' h', ←
    h₂']
  exact Simplex.mem_circumsphere _ _
  -- 🎉 no goals
#align affine.triangle.mem_circumsphere_of_two_zsmul_oangle_eq Affine.Triangle.mem_circumsphere_of_two_zsmul_oangle_eq

end Triangle

end Affine

namespace EuclideanGeometry

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

local notation "o" => Module.Oriented.positiveOrientation

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π. -/
theorem cospherical_of_two_zsmul_oangle_eq_of_not_collinear {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) (hn : ¬Collinear ℝ ({p₁, p₂, p₄} : Set P)) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) := by
  have hn' : ¬Collinear ℝ ({p₁, p₃, p₄} : Set P) := by
    rwa [← collinear_iff_of_two_zsmul_oangle_eq h]
  let t₁ : Affine.Triangle ℝ P := ⟨![p₁, p₂, p₄], affineIndependent_iff_not_collinear_set.2 hn⟩
  -- ⊢ Cospherical {p₁, p₂, p₃, p₄}
  let t₂ : Affine.Triangle ℝ P := ⟨![p₁, p₃, p₄], affineIndependent_iff_not_collinear_set.2 hn'⟩
  -- ⊢ Cospherical {p₁, p₂, p₃, p₄}
  rw [cospherical_iff_exists_sphere]
  -- ⊢ ∃ s, {p₁, p₂, p₃, p₄} ⊆ Metric.sphere s.center s.radius
  refine' ⟨t₂.circumsphere, _⟩
  -- ⊢ {p₁, p₂, p₃, p₄} ⊆ Metric.sphere (Affine.Simplex.circumsphere t₂).center (Af …
  simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff]
  -- ⊢ p₁ ∈ Metric.sphere (Affine.Simplex.circumsphere { points := ![p₁, p₃, p₄], I …
  refine' ⟨t₂.mem_circumsphere 0, _, t₂.mem_circumsphere 1, t₂.mem_circumsphere 2⟩
  -- ⊢ p₂ ∈ Metric.sphere (Affine.Simplex.circumsphere { points := ![p₁, p₃, p₄], I …
  rw [Affine.Triangle.circumsphere_eq_circumsphere_of_eq_of_eq_of_two_zsmul_oangle_eq
    (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2) (by decide)
    (show t₂.points 0 = t₁.points 0 from rfl) rfl h.symm]
  exact t₁.mem_circumsphere 1
  -- 🎉 no goals
#align euclidean_geometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π, with a "concyclic" conclusion. -/
theorem concyclic_of_two_zsmul_oangle_eq_of_not_collinear {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) (hn : ¬Collinear ℝ ({p₁, p₂, p₄} : Set P)) :
    Concyclic ({p₁, p₂, p₃, p₄} : Set P) :=
  ⟨cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hn, coplanar_of_fact_finrank_eq_two _⟩
#align euclidean_geometry.concyclic_of_two_zsmul_oangle_eq_of_not_collinear EuclideanGeometry.concyclic_of_two_zsmul_oangle_eq_of_not_collinear

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π, with a "cospherical or collinear" conclusion. -/
theorem cospherical_or_collinear_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) :
    Cospherical ({p₁, p₂, p₃, p₄} : Set P) ∨ Collinear ℝ ({p₁, p₂, p₃, p₄} : Set P) := by
  by_cases hc : Collinear ℝ ({p₁, p₂, p₄} : Set P)
  -- ⊢ Cospherical {p₁, p₂, p₃, p₄} ∨ Collinear ℝ {p₁, p₂, p₃, p₄}
  · by_cases he : p₁ = p₄
    -- ⊢ Cospherical {p₁, p₂, p₃, p₄} ∨ Collinear ℝ {p₁, p₂, p₃, p₄}
    · rw [he, Set.insert_eq_self.2
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))]
      by_cases hl : Collinear ℝ ({p₂, p₃, p₄} : Set P); · exact Or.inr hl
      -- ⊢ Cospherical {p₂, p₃, p₄} ∨ Collinear ℝ {p₂, p₃, p₄}
                                                          -- 🎉 no goals
      rw [or_iff_left hl]
      -- ⊢ Cospherical {p₂, p₃, p₄}
      let t : Affine.Triangle ℝ P := ⟨![p₂, p₃, p₄], affineIndependent_iff_not_collinear_set.2 hl⟩
      -- ⊢ Cospherical {p₂, p₃, p₄}
      rw [cospherical_iff_exists_sphere]
      -- ⊢ ∃ s, {p₂, p₃, p₄} ⊆ Metric.sphere s.center s.radius
      refine' ⟨t.circumsphere, _⟩
      -- ⊢ {p₂, p₃, p₄} ⊆ Metric.sphere (Affine.Simplex.circumsphere t).center (Affine. …
      simp_rw [Set.insert_subset_iff, Set.singleton_subset_iff]
      -- ⊢ p₂ ∈ Metric.sphere (Affine.Simplex.circumsphere { points := ![p₂, p₃, p₄], I …
      exact ⟨t.mem_circumsphere 0, t.mem_circumsphere 1, t.mem_circumsphere 2⟩
      -- 🎉 no goals
    have hc' : Collinear ℝ ({p₁, p₃, p₄} : Set P) := by
      rwa [← collinear_iff_of_two_zsmul_oangle_eq h]
    refine' Or.inr _
    -- ⊢ Collinear ℝ {p₁, p₂, p₃, p₄}
    rw [Set.insert_comm p₁ p₂] at hc
    -- ⊢ Collinear ℝ {p₁, p₂, p₃, p₄}
    rwa [Set.insert_comm p₁ p₂, hc'.collinear_insert_iff_of_ne (Set.mem_insert _ _)
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) he]
  · exact Or.inl (cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hc)
    -- 🎉 no goals
#align euclidean_geometry.cospherical_or_collinear_of_two_zsmul_oangle_eq EuclideanGeometry.cospherical_or_collinear_of_two_zsmul_oangle_eq

/-- Converse of "angles in same segment are equal" and "opposite angles of a cyclic quadrilateral
add to π", for oriented angles mod π, with a "concyclic or collinear" conclusion. -/
theorem concyclic_or_collinear_of_two_zsmul_oangle_eq {p₁ p₂ p₃ p₄ : P}
    (h : (2 : ℤ) • ∡ p₁ p₂ p₄ = (2 : ℤ) • ∡ p₁ p₃ p₄) :
    Concyclic ({p₁, p₂, p₃, p₄} : Set P) ∨ Collinear ℝ ({p₁, p₂, p₃, p₄} : Set P) := by
  rcases cospherical_or_collinear_of_two_zsmul_oangle_eq h with (hc | hc)
  -- ⊢ Concyclic {p₁, p₂, p₃, p₄} ∨ Collinear ℝ {p₁, p₂, p₃, p₄}
  · exact Or.inl ⟨hc, coplanar_of_fact_finrank_eq_two _⟩
    -- 🎉 no goals
  · exact Or.inr hc
    -- 🎉 no goals
#align euclidean_geometry.concyclic_or_collinear_of_two_zsmul_oangle_eq EuclideanGeometry.concyclic_or_collinear_of_two_zsmul_oangle_eq

end EuclideanGeometry
