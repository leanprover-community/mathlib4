/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

/-!
# Rotations by oriented angles.

This file defines rotations by oriented angles in real inner product spaces.

## Main definitions

* `Orientation.rotation` is the rotation by an oriented angle with respect to an orientation.

-/


noncomputable section

open Module Complex

open scoped Real RealInnerProductSpace ComplexConjugate

namespace Orientation

attribute [local instance] Complex.finrank_real_complex_fact

variable {V V' : Type*}
variable [NormedAddCommGroup V] [NormedAddCommGroup V']
variable [InnerProductSpace ℝ V] [InnerProductSpace ℝ V']
variable [Fact (finrank ℝ V = 2)] [Fact (finrank ℝ V' = 2)] (o : Orientation ℝ V (Fin 2))

local notation "J" => o.rightAngleRotation

/-- Auxiliary construction to build a rotation by the oriented angle `θ`. -/
def rotationAux (θ : Real.Angle) : V →ₗᵢ[ℝ] V :=
  LinearMap.isometryOfInner
    (Real.Angle.cos θ • LinearMap.id +
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      intro x y
      simp only [RCLike.conj_to_real, id, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.id_coe, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
        Orientation.areaForm_rightAngleRotation_left, Orientation.inner_rightAngleRotation_left,
        Orientation.inner_rightAngleRotation_right, inner_add_left, inner_smul_left,
        inner_add_right, inner_smul_right]
      linear_combination ⟪x, y⟫ * θ.cos_sq_add_sin_sq)

@[simp]
theorem rotationAux_apply (θ : Real.Angle) (x : V) :
    o.rotationAux θ x = Real.Angle.cos θ • x + Real.Angle.sin θ • J x :=
  rfl

/-- A rotation by the oriented angle `θ`. -/
def rotation (θ : Real.Angle) : V ≃ₗᵢ[ℝ] V :=
  LinearIsometryEquiv.ofLinearIsometry (o.rotationAux θ)
    (Real.Angle.cos θ • LinearMap.id -
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      ext x
      convert congr_arg (fun t : ℝ => t • x) θ.cos_sq_add_sin_sq using 1
      · simp only [o.rightAngleRotation_rightAngleRotation, o.rotationAux_apply,
          Function.comp_apply, id, LinearEquiv.coe_coe, LinearIsometry.coe_toLinearMap,
          LinearIsometryEquiv.coe_toLinearEquiv, map_smul, map_sub, LinearMap.coe_comp,
          LinearMap.id_coe, LinearMap.smul_apply, LinearMap.sub_apply]
        module
      · simp)
    (by
      ext x
      convert congr_arg (fun t : ℝ => t • x) θ.cos_sq_add_sin_sq using 1
      · simp only [o.rightAngleRotation_rightAngleRotation, o.rotationAux_apply,
          Function.comp_apply, id, LinearEquiv.coe_coe, LinearIsometry.coe_toLinearMap,
          LinearIsometryEquiv.coe_toLinearEquiv, map_add, map_smul, LinearMap.coe_comp,
          LinearMap.id_coe, LinearMap.smul_apply, LinearMap.sub_apply]
        module
      · simp)

theorem rotation_apply (θ : Real.Angle) (x : V) :
    o.rotation θ x = Real.Angle.cos θ • x + Real.Angle.sin θ • J x :=
  rfl

theorem rotation_symm_apply (θ : Real.Angle) (x : V) :
    (o.rotation θ).symm x = Real.Angle.cos θ • x - Real.Angle.sin θ • J x :=
  rfl

theorem rotation_eq_matrix_toLin (θ : Real.Angle) {x : V} (hx : x ≠ 0) :
    (o.rotation θ).toLinearMap =
      Matrix.toLin (o.basisRightAngleRotation x hx) (o.basisRightAngleRotation x hx)
        !![θ.cos, -θ.sin; θ.sin, θ.cos] := by
  apply (o.basisRightAngleRotation x hx).ext
  intro i
  fin_cases i
  · rw [Matrix.toLin_self]
    simp [rotation_apply, Fin.sum_univ_succ]
  · rw [Matrix.toLin_self]
    simp [rotation_apply, Fin.sum_univ_succ, add_comm]

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp]
theorem det_rotation (θ : Real.Angle) : LinearMap.det (o.rotation θ).toLinearMap = 1 := by
  haveI : Nontrivial V := nontrivial_of_finrank_eq_succ (@Fact.out (finrank ℝ V = 2) _)
  obtain ⟨x, hx⟩ : ∃ x, x ≠ (0 : V) := exists_ne (0 : V)
  rw [o.rotation_eq_matrix_toLin θ hx]
  simpa [sq] using θ.cos_sq_add_sin_sq

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp]
theorem linearEquiv_det_rotation (θ : Real.Angle) :
    LinearEquiv.det (o.rotation θ).toLinearEquiv = 1 :=
  Units.ext <| by
    -- Porting note: Lean can't see through `LinearEquiv.coe_det` and needed the rewrite
    -- in mathlib3 this was just `units.ext <| o.det_rotation θ`
    simpa only [LinearEquiv.coe_det, Units.val_one] using o.det_rotation θ

/-- The inverse of `rotation` is rotation by the negation of the angle. -/
@[simp]
theorem rotation_symm (θ : Real.Angle) : (o.rotation θ).symm = o.rotation (-θ) := by
  ext; simp [o.rotation_apply, o.rotation_symm_apply, sub_eq_add_neg]

/-- Rotation by 0 is the identity. -/
@[simp]
theorem rotation_zero : o.rotation 0 = LinearIsometryEquiv.refl ℝ V := by ext; simp [rotation]

/-- Rotation by π is negation. -/
@[simp]
theorem rotation_pi : o.rotation π = LinearIsometryEquiv.neg ℝ := by
  ext x
  simp [rotation]

/-- Rotation by π is negation. -/
theorem rotation_pi_apply (x : V) : o.rotation π x = -x := by simp

/-- Rotation by π / 2 is the "right-angle-rotation" map `J`. -/
theorem rotation_pi_div_two : o.rotation (π / 2 : ℝ) = J := by
  ext x
  simp [rotation]

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp]
theorem rotation_rotation (θ₁ θ₂ : Real.Angle) (x : V) :
    o.rotation θ₁ (o.rotation θ₂ x) = o.rotation (θ₁ + θ₂) x := by
  simp only [o.rotation_apply, Real.Angle.cos_add, Real.Angle.sin_add, LinearIsometryEquiv.map_add,
    LinearIsometryEquiv.trans_apply, map_smul, rightAngleRotation_rightAngleRotation]
  module

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp]
theorem rotation_trans (θ₁ θ₂ : Real.Angle) :
    (o.rotation θ₁).trans (o.rotation θ₂) = o.rotation (θ₂ + θ₁) :=
  LinearIsometryEquiv.ext fun _ => by rw [← rotation_rotation, LinearIsometryEquiv.trans_apply]

/-- Rotating the first of two vectors by `θ` scales their Kahler form by `cos θ - sin θ * I`. -/
@[simp]
theorem kahler_rotation_left (x y : V) (θ : Real.Angle) :
    o.kahler (o.rotation θ x) y = conj (θ.toCircle : ℂ) * o.kahler x y := by
  -- Porting note: this needed the `Complex.conj_ofReal` instead of `RCLike.conj_ofReal`;
  -- I believe this is because the respective coercions are no longer defeq, and
  -- `Real.Angle.coe_toCircle` uses the `Complex` version.
  simp only [o.rotation_apply, map_add, map_mul, LinearMap.map_smulₛₗ, RingHom.id_apply,
    LinearMap.add_apply, LinearMap.smul_apply, real_smul, kahler_rightAngleRotation_left,
    Real.Angle.coe_toCircle, Complex.conj_ofReal, conj_I]
  ring

/-- Negating a rotation is equivalent to rotation by π plus the angle. -/
theorem neg_rotation (θ : Real.Angle) (x : V) : -o.rotation θ x = o.rotation (π + θ) x := by
  rw [← o.rotation_pi_apply, rotation_rotation]

/-- Negating a rotation by -π / 2 is equivalent to rotation by π / 2. -/
@[simp]
theorem neg_rotation_neg_pi_div_two (x : V) :
    -o.rotation (-π / 2 : ℝ) x = o.rotation (π / 2 : ℝ) x := by
  rw [neg_rotation, ← Real.Angle.coe_add, neg_div, ← sub_eq_add_neg, sub_half]

/-- Negating a rotation by π / 2 is equivalent to rotation by -π / 2. -/
theorem neg_rotation_pi_div_two (x : V) : -o.rotation (π / 2 : ℝ) x = o.rotation (-π / 2 : ℝ) x :=
  (neg_eq_iff_eq_neg.mp <| o.neg_rotation_neg_pi_div_two _).symm

/-- Rotating the first of two vectors by `θ` scales their Kahler form by `cos (-θ) + sin (-θ) * I`.
-/
theorem kahler_rotation_left' (x y : V) (θ : Real.Angle) :
    o.kahler (o.rotation θ x) y = (-θ).toCircle * o.kahler x y := by
  simp only [Real.Angle.toCircle_neg, Circle.coe_inv_eq_conj, kahler_rotation_left]

/-- Rotating the second of two vectors by `θ` scales their Kahler form by `cos θ + sin θ * I`. -/
@[simp]
theorem kahler_rotation_right (x y : V) (θ : Real.Angle) :
    o.kahler x (o.rotation θ y) = θ.toCircle * o.kahler x y := by
  simp only [o.rotation_apply, map_add, LinearMap.map_smulₛₗ, RingHom.id_apply, real_smul,
    kahler_rightAngleRotation_right, Real.Angle.coe_toCircle]
  ring

/-- Rotating the first vector by `θ` subtracts `θ` from the angle between two vectors. -/
@[simp]
theorem oangle_rotation_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) y = o.oangle x y - θ := by
  simp only [oangle, o.kahler_rotation_left']
  rw [Complex.arg_mul_coe_angle, Real.Angle.arg_toCircle]
  · abel
  · exact Circle.coe_ne_zero _
  · exact o.kahler_ne_zero hx hy

/-- Rotating the second vector by `θ` adds `θ` to the angle between two vectors. -/
@[simp]
theorem oangle_rotation_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    o.oangle x (o.rotation θ y) = o.oangle x y + θ := by
  simp only [oangle, o.kahler_rotation_right]
  rw [Complex.arg_mul_coe_angle, Real.Angle.arg_toCircle]
  · abel
  · exact Circle.coe_ne_zero _
  · exact o.kahler_ne_zero hx hy

/-- The rotation of a vector by `θ` has an angle of `-θ` from that vector. -/
theorem oangle_rotation_self_left {x : V} (hx : x ≠ 0) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) x = -θ := by simp [hx]

/-- A vector has an angle of `θ` from the rotation of that vector by `θ`. -/
theorem oangle_rotation_self_right {x : V} (hx : x ≠ 0) (θ : Real.Angle) :
    o.oangle x (o.rotation θ x) = θ := by simp [hx]

/-- Rotating the first vector by the angle between the two vectors results in an angle of 0. -/
@[simp]
theorem oangle_rotation_oangle_left (x y : V) : o.oangle (o.rotation (o.oangle x y) x) y = 0 := by
  by_cases hx : x = 0
  · simp [hx]
  · by_cases hy : y = 0
    · simp [hy]
    · simp [hx, hy]

/-- Rotating the first vector by the angle between the two vectors and swapping the vectors
results in an angle of 0. -/
@[simp]
theorem oangle_rotation_oangle_right (x y : V) : o.oangle y (o.rotation (o.oangle x y) x) = 0 := by
  rw [oangle_rev]
  simp

/-- Rotating both vectors by the same angle does not change the angle between those vectors. -/
@[simp]
theorem oangle_rotation (x y : V) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) (o.rotation θ y) = o.oangle x y := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]

/-- A rotation of a nonzero vector equals that vector if and only if the angle is zero. -/
@[simp]
theorem rotation_eq_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : Real.Angle) :
    o.rotation θ x = x ↔ θ = 0 := by
  constructor
  · intro h
    rw [eq_comm]
    simpa [hx, h] using o.oangle_rotation_right hx hx θ
  · intro h
    simp [h]

/-- A nonzero vector equals a rotation of that vector if and only if the angle is zero. -/
@[simp]
theorem eq_rotation_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : Real.Angle) :
    x = o.rotation θ x ↔ θ = 0 := by rw [← o.rotation_eq_self_iff_angle_eq_zero hx, eq_comm]

/-- A rotation of a vector equals that vector if and only if the vector or the angle is zero. -/
theorem rotation_eq_self_iff (x : V) (θ : Real.Angle) : o.rotation θ x = x ↔ x = 0 ∨ θ = 0 := by
  by_cases h : x = 0 <;> simp [h]

/-- A vector equals a rotation of that vector if and only if the vector or the angle is zero. -/
theorem eq_rotation_self_iff (x : V) (θ : Real.Angle) : x = o.rotation θ x ↔ x = 0 ∨ θ = 0 := by
  rw [← rotation_eq_self_iff, eq_comm]

/-- Rotating a vector by the angle to another vector gives the second vector if and only if the
norms are equal. -/
@[simp]
theorem rotation_oangle_eq_iff_norm_eq (x y : V) : o.rotation (o.oangle x y) x = y ↔ ‖x‖ = ‖y‖ := by
  constructor
  · intro h
    rw [← h, LinearIsometryEquiv.norm_map]
  · intro h
    rw [o.eq_iff_oangle_eq_zero_of_norm_eq] <;> simp [h]

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by the ratio of the norms. -/
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (θ : Real.Angle) : o.oangle x y = θ ↔ y = (‖y‖ / ‖x‖) • o.rotation θ x := by
  have hp := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx)
  constructor
  · rintro rfl
    rw [← LinearIsometryEquiv.map_smul, ← o.oangle_smul_left_of_pos x y hp, eq_comm,
      rotation_oangle_eq_iff_norm_eq, norm_smul, Real.norm_of_nonneg hp.le,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hx)]
  · intro hye
    rw [hye, o.oangle_smul_right_of_pos _ _ hp, o.oangle_rotation_self_right hx]

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by a positive real. -/
theorem oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (θ : Real.Angle) : o.oangle x y = θ ↔ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x := by
  constructor
  · intro h
    rw [o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy] at h
    exact ⟨‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx), h⟩
  · rintro ⟨r, hr, rfl⟩
    rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right hx]

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by the ratio of the norms, or `θ` and at least one of the
vectors are zero. -/
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
    o.oangle x y = θ ↔
      x ≠ 0 ∧ y ≠ 0 ∧ y = (‖y‖ / ‖x‖) • o.rotation θ x ∨ θ = 0 ∧ (x = 0 ∨ y = 0) := by
  by_cases hx : x = 0
  · simp [hx, eq_comm]
  · by_cases hy : y = 0
    · simp [hy, eq_comm]
    · rw [o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy]
      simp [hx, hy]

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by a positive real, or `θ` and at least one of the
vectors are zero. -/
theorem oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
    o.oangle x y = θ ↔
      (x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x) ∨ θ = 0 ∧ (x = 0 ∨ y = 0) := by
  by_cases hx : x = 0
  · simp [hx, eq_comm]
  · by_cases hy : y = 0
    · simp [hy, eq_comm]
    · rw [o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero hx hy]
      simp [hx, hy]

/-- Any linear isometric equivalence in `V` with positive determinant is `rotation`. -/
theorem exists_linearIsometryEquiv_eq_of_det_pos {f : V ≃ₗᵢ[ℝ] V}
    (hd : 0 < LinearMap.det (f.toLinearEquiv : V →ₗ[ℝ] V)) :
    ∃ θ : Real.Angle, f = o.rotation θ := by
  haveI : Nontrivial V := nontrivial_of_finrank_eq_succ (@Fact.out (finrank ℝ V = 2) _)
  obtain ⟨x, hx⟩ : ∃ x, x ≠ (0 : V) := exists_ne (0 : V)
  use o.oangle x (f x)
  apply LinearIsometryEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply (o.basisRightAngleRotation x hx).ext
  intro i
  symm
  fin_cases i
  · simp
  have : o.oangle (J x) (f (J x)) = o.oangle x (f x) := by
    simp only [oangle, o.linearIsometryEquiv_comp_rightAngleRotation f hd,
      o.kahler_comp_rightAngleRotation]
  simp [← this]

theorem rotation_map (θ : Real.Angle) (f : V ≃ₗᵢ[ℝ] V') (x : V') :
    (Orientation.map (Fin 2) f.toLinearEquiv o).rotation θ x = f (o.rotation θ (f.symm x)) := by
  simp [rotation_apply, o.rightAngleRotation_map]

@[simp]
protected theorem _root_.Complex.rotation (θ : Real.Angle) (z : ℂ) :
    Complex.orientation.rotation θ z = θ.toCircle * z := by
  simp only [rotation_apply, Complex.rightAngleRotation, Real.Angle.coe_toCircle, real_smul]
  ring

/-- Rotation in an oriented real inner product space of dimension 2 can be evaluated in terms of a
complex-number representation of the space. -/
theorem rotation_map_complex (θ : Real.Angle) (f : V ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x : V) :
    f (o.rotation θ x) = θ.toCircle * f x := by
  rw [← Complex.rotation, ← hf, o.rotation_map, LinearIsometryEquiv.symm_apply_apply]

/-- Negating the orientation negates the angle in `rotation`. -/
theorem rotation_neg_orientation_eq_neg (θ : Real.Angle) : (-o).rotation θ = o.rotation (-θ) :=
  LinearIsometryEquiv.ext <| by simp [rotation_apply]

/-- The inner product between a `π / 2` rotation of a vector and that vector is zero. -/
@[simp]
theorem inner_rotation_pi_div_two_left (x : V) : ⟪o.rotation (π / 2 : ℝ) x, x⟫ = 0 := by
  rw [rotation_pi_div_two, inner_rightAngleRotation_self]

/-- The inner product between a vector and a `π / 2` rotation of that vector is zero. -/
@[simp]
theorem inner_rotation_pi_div_two_right (x : V) : ⟪x, o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_rotation_pi_div_two_left]

/-- The inner product between a multiple of a `π / 2` rotation of a vector and that vector is
zero. -/
@[simp]
theorem inner_smul_rotation_pi_div_two_left (x : V) (r : ℝ) :
    ⟪r • o.rotation (π / 2 : ℝ) x, x⟫ = 0 := by
  rw [inner_smul_left, inner_rotation_pi_div_two_left, mul_zero]

/-- The inner product between a vector and a multiple of a `π / 2` rotation of that vector is
zero. -/
@[simp]
theorem inner_smul_rotation_pi_div_two_right (x : V) (r : ℝ) :
    ⟪x, r • o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_smul_rotation_pi_div_two_left]

/-- The inner product between a `π / 2` rotation of a vector and a multiple of that vector is
zero. -/
@[simp]
theorem inner_rotation_pi_div_two_left_smul (x : V) (r : ℝ) :
    ⟪o.rotation (π / 2 : ℝ) x, r • x⟫ = 0 := by
  rw [inner_smul_right, inner_rotation_pi_div_two_left, mul_zero]

/-- The inner product between a multiple of a vector and a `π / 2` rotation of that vector is
zero. -/
@[simp]
theorem inner_rotation_pi_div_two_right_smul (x : V) (r : ℝ) :
    ⟪r • x, o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_rotation_pi_div_two_left_smul]

/-- The inner product between a multiple of a `π / 2` rotation of a vector and a multiple of
that vector is zero. -/
@[simp]
theorem inner_smul_rotation_pi_div_two_smul_left (x : V) (r₁ r₂ : ℝ) :
    ⟪r₁ • o.rotation (π / 2 : ℝ) x, r₂ • x⟫ = 0 := by
  rw [inner_smul_right, inner_smul_rotation_pi_div_two_left, mul_zero]

/-- The inner product between a multiple of a vector and a multiple of a `π / 2` rotation of
that vector is zero. -/
@[simp]
theorem inner_smul_rotation_pi_div_two_smul_right (x : V) (r₁ r₂ : ℝ) :
    ⟪r₂ • x, r₁ • o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_smul_rotation_pi_div_two_smul_left]

/-- The inner product between two vectors is zero if and only if the first vector is zero or
the second is a multiple of a `π / 2` rotation of that vector. -/
theorem inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two {x y : V} :
    ⟪x, y⟫ = 0 ↔ x = 0 ∨ ∃ r : ℝ, r • o.rotation (π / 2 : ℝ) x = y := by
  rw [← o.eq_zero_or_oangle_eq_iff_inner_eq_zero]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with (rfl | rfl | h | h)
    · exact Or.inl rfl
    · exact Or.inr ⟨0, zero_smul _ _⟩
    · obtain ⟨r, _, rfl⟩ :=
        (o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero (o.left_ne_zero_of_oangle_eq_pi_div_two h)
          (o.right_ne_zero_of_oangle_eq_pi_div_two h) _).1 h
      exact Or.inr ⟨r, rfl⟩
    · obtain ⟨r, _, rfl⟩ :=
        (o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero
          (o.left_ne_zero_of_oangle_eq_neg_pi_div_two h)
          (o.right_ne_zero_of_oangle_eq_neg_pi_div_two h) _).1 h
      refine Or.inr ⟨-r, ?_⟩
      rw [neg_smul, ← smul_neg, o.neg_rotation_pi_div_two]
  · rcases h with (rfl | ⟨r, rfl⟩)
    · exact Or.inl rfl
    · by_cases hx : x = 0; · exact Or.inl hx
      rcases lt_trichotomy r 0 with (hr | rfl | hr)
      · refine Or.inr (Or.inr (Or.inr ?_))
        rw [o.oangle_smul_right_of_neg _ _ hr, o.neg_rotation_pi_div_two,
          o.oangle_rotation_self_right hx]
      · exact Or.inr (Or.inl (zero_smul _ _))
      · refine Or.inr (Or.inr (Or.inl ?_))
        rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right hx]

end Orientation
