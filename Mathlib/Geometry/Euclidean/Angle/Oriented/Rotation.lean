/-
Copyright (c) 2022 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Heather Macbeth
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

#align_import geometry.euclidean.angle.oriented.rotation from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Rotations by oriented angles.

This file defines rotations by oriented angles in real inner product spaces.

## Main definitions

* `Orientation.rotation` is the rotation by an oriented angle with respect to an orientation.

-/


noncomputable section

open FiniteDimensional Complex

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
      -- ⊢ inner (↑(Real.Angle.cos θ • LinearMap.id + Real.Angle.sin θ • ↑(rightAngleRo …
      simp only [IsROrC.conj_to_real, id.def, LinearMap.smul_apply, LinearMap.add_apply,
        LinearMap.id_coe, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
        Orientation.areaForm_rightAngleRotation_left, Orientation.inner_rightAngleRotation_left,
        Orientation.inner_rightAngleRotation_right, inner_add_left, inner_smul_left,
        inner_add_right, inner_smul_right]
      linear_combination inner (𝕜 := ℝ) x y * θ.cos_sq_add_sin_sq)
      -- 🎉 no goals
#align orientation.rotation_aux Orientation.rotationAux

@[simp]
theorem rotationAux_apply (θ : Real.Angle) (x : V) :
    o.rotationAux θ x = Real.Angle.cos θ • x + Real.Angle.sin θ • J x :=
  rfl
#align orientation.rotation_aux_apply Orientation.rotationAux_apply

/-- A rotation by the oriented angle `θ`. -/
def rotation (θ : Real.Angle) : V ≃ₗᵢ[ℝ] V :=
  LinearIsometryEquiv.ofLinearIsometry (o.rotationAux θ)
    (Real.Angle.cos θ • LinearMap.id -
      Real.Angle.sin θ • (LinearIsometryEquiv.toLinearEquiv J).toLinearMap)
    (by
      ext x
      -- ⊢ ↑(LinearMap.comp (rotationAux o θ).toLinearMap (Real.Angle.cos θ • LinearMap …
      convert congr_arg (fun t : ℝ => t • x) θ.cos_sq_add_sin_sq using 1
      -- ⊢ ↑(LinearMap.comp (rotationAux o θ).toLinearMap (Real.Angle.cos θ • LinearMap …
      · simp only [o.rightAngleRotation_rightAngleRotation, o.rotationAux_apply,
          Function.comp_apply, id.def, LinearEquiv.coe_coe, LinearIsometry.coe_toLinearMap,
          LinearIsometryEquiv.coe_toLinearEquiv, map_smul, map_sub, LinearMap.coe_comp,
          LinearMap.id_coe, LinearMap.smul_apply, LinearMap.sub_apply, ← mul_smul, add_smul,
          smul_add, smul_neg, smul_sub, mul_comm, sq]
        abel
        -- 🎉 no goals
        -- 🎉 no goals
      · simp)
        -- 🎉 no goals
    (by
      ext x
      -- ⊢ ↑(LinearMap.comp (Real.Angle.cos θ • LinearMap.id - Real.Angle.sin θ • ↑(rig …
      convert congr_arg (fun t : ℝ => t • x) θ.cos_sq_add_sin_sq using 1
      -- ⊢ ↑(LinearMap.comp (Real.Angle.cos θ • LinearMap.id - Real.Angle.sin θ • ↑(rig …
      · simp only [o.rightAngleRotation_rightAngleRotation, o.rotationAux_apply,
          Function.comp_apply, id.def, LinearEquiv.coe_coe, LinearIsometry.coe_toLinearMap,
          LinearIsometryEquiv.coe_toLinearEquiv, map_add, map_smul, LinearMap.coe_comp,
          LinearMap.id_coe, LinearMap.smul_apply, LinearMap.sub_apply,
          add_smul, smul_neg, smul_sub, smul_smul]
        ring_nf
        -- ⊢ Real.Angle.cos θ ^ 2 • x - (Real.Angle.cos θ * Real.Angle.sin θ) • ↑(rightAn …
        abel
        -- 🎉 no goals
        -- 🎉 no goals
      · simp)
        -- 🎉 no goals
#align orientation.rotation Orientation.rotation

theorem rotation_apply (θ : Real.Angle) (x : V) :
    o.rotation θ x = Real.Angle.cos θ • x + Real.Angle.sin θ • J x :=
  rfl
#align orientation.rotation_apply Orientation.rotation_apply

theorem rotation_symm_apply (θ : Real.Angle) (x : V) :
    (o.rotation θ).symm x = Real.Angle.cos θ • x - Real.Angle.sin θ • J x :=
  rfl
#align orientation.rotation_symm_apply Orientation.rotation_symm_apply

theorem rotation_eq_matrix_toLin (θ : Real.Angle) {x : V} (hx : x ≠ 0) :
    (o.rotation θ).toLinearMap =
      Matrix.toLin (o.basisRightAngleRotation x hx) (o.basisRightAngleRotation x hx)
        !![θ.cos, -θ.sin; θ.sin, θ.cos] := by
  apply (o.basisRightAngleRotation x hx).ext
  -- ⊢ ∀ (i : Fin 2), ↑↑(rotation o θ).toLinearEquiv (↑(basisRightAngleRotation o x …
  intro i
  -- ⊢ ↑↑(rotation o θ).toLinearEquiv (↑(basisRightAngleRotation o x hx) i) = ↑(↑(M …
  fin_cases i
  -- ⊢ ↑↑(rotation o θ).toLinearEquiv (↑(basisRightAngleRotation o x hx) { val := 0 …
  · rw [Matrix.toLin_self]
    -- ⊢ ↑↑(rotation o θ).toLinearEquiv (↑(basisRightAngleRotation o x hx) { val := 0 …
    simp [rotation_apply, Fin.sum_univ_succ]
    -- 🎉 no goals
  · rw [Matrix.toLin_self]
    -- ⊢ ↑↑(rotation o θ).toLinearEquiv (↑(basisRightAngleRotation o x hx) { val := 1 …
    simp [rotation_apply, Fin.sum_univ_succ, add_comm]
    -- 🎉 no goals
#align orientation.rotation_eq_matrix_to_lin Orientation.rotation_eq_matrix_toLin

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp]
theorem det_rotation (θ : Real.Angle) : LinearMap.det (o.rotation θ).toLinearMap = 1 := by
  haveI : Nontrivial V :=
    FiniteDimensional.nontrivial_of_finrank_eq_succ (@Fact.out (finrank ℝ V = 2) _)
  obtain ⟨x, hx⟩ : ∃ x, x ≠ (0 : V) := exists_ne (0 : V)
  -- ⊢ ↑LinearMap.det ↑(rotation o θ).toLinearEquiv = 1
  rw [o.rotation_eq_matrix_toLin θ hx]
  -- ⊢ ↑LinearMap.det (↑(Matrix.toLin (basisRightAngleRotation o x hx) (basisRightA …
  simpa [sq] using θ.cos_sq_add_sin_sq
  -- 🎉 no goals
#align orientation.det_rotation Orientation.det_rotation

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp]
theorem linearEquiv_det_rotation (θ : Real.Angle) :
    LinearEquiv.det (o.rotation θ).toLinearEquiv = 1 :=
  Units.ext <| by
    -- porting note: Lean can't see through `LinearEquiv.coe_det` and needed the rewrite
    -- in mathlib3 this was just `units.ext $ o.det_rotation θ`
    simpa only [LinearEquiv.coe_det, Units.val_one] using o.det_rotation θ
    -- 🎉 no goals
#align orientation.linear_equiv_det_rotation Orientation.linearEquiv_det_rotation

/-- The inverse of `rotation` is rotation by the negation of the angle. -/
@[simp]
theorem rotation_symm (θ : Real.Angle) : (o.rotation θ).symm = o.rotation (-θ) := by
  ext; simp [o.rotation_apply, o.rotation_symm_apply, sub_eq_add_neg]
  -- ⊢ ↑(LinearIsometryEquiv.symm (rotation o θ)) x✝ = ↑(rotation o (-θ)) x✝
       -- 🎉 no goals
#align orientation.rotation_symm Orientation.rotation_symm

/-- Rotation by 0 is the identity. -/
@[simp]
theorem rotation_zero : o.rotation 0 = LinearIsometryEquiv.refl ℝ V := by ext; simp [rotation]
                                                                          -- ⊢ ↑(rotation o 0) x✝ = ↑(LinearIsometryEquiv.refl ℝ V) x✝
                                                                               -- 🎉 no goals
#align orientation.rotation_zero Orientation.rotation_zero

/-- Rotation by π is negation. -/
@[simp]
theorem rotation_pi : o.rotation π = LinearIsometryEquiv.neg ℝ := by
  ext x
  -- ⊢ ↑(rotation o ↑π) x = ↑(LinearIsometryEquiv.neg ℝ) x
  simp [rotation]
  -- 🎉 no goals
#align orientation.rotation_pi Orientation.rotation_pi

/-- Rotation by π is negation. -/
theorem rotation_pi_apply (x : V) : o.rotation π x = -x := by simp
                                                              -- 🎉 no goals
#align orientation.rotation_pi_apply Orientation.rotation_pi_apply

/-- Rotation by π / 2 is the "right-angle-rotation" map `J`. -/
theorem rotation_pi_div_two : o.rotation (π / 2 : ℝ) = J := by
  ext x
  -- ⊢ ↑(rotation o ↑(π / 2)) x = ↑(rightAngleRotation o) x
  simp [rotation]
  -- 🎉 no goals
#align orientation.rotation_pi_div_two Orientation.rotation_pi_div_two

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp]
theorem rotation_rotation (θ₁ θ₂ : Real.Angle) (x : V) :
    o.rotation θ₁ (o.rotation θ₂ x) = o.rotation (θ₁ + θ₂) x := by
  simp only [o.rotation_apply, ← mul_smul, Real.Angle.cos_add, Real.Angle.sin_add, add_smul,
    sub_smul, LinearIsometryEquiv.trans_apply, smul_add, LinearIsometryEquiv.map_add,
    LinearIsometryEquiv.map_smul, rightAngleRotation_rightAngleRotation, smul_neg]
  ring_nf
  -- ⊢ (Real.Angle.cos θ₂ * Real.Angle.cos θ₁) • x + (Real.Angle.cos θ₂ * Real.Angl …
  abel
  -- 🎉 no goals
  -- 🎉 no goals
#align orientation.rotation_rotation Orientation.rotation_rotation

/-- Rotating twice is equivalent to rotating by the sum of the angles. -/
@[simp]
theorem rotation_trans (θ₁ θ₂ : Real.Angle) :
    (o.rotation θ₁).trans (o.rotation θ₂) = o.rotation (θ₂ + θ₁) :=
  LinearIsometryEquiv.ext fun _ => by rw [← rotation_rotation, LinearIsometryEquiv.trans_apply]
                                      -- 🎉 no goals
#align orientation.rotation_trans Orientation.rotation_trans

/-- Rotating the first of two vectors by `θ` scales their Kahler form by `cos θ - sin θ * I`. -/
@[simp]
theorem kahler_rotation_left (x y : V) (θ : Real.Angle) :
    o.kahler (o.rotation θ x) y = conj (θ.expMapCircle : ℂ) * o.kahler x y := by
  -- porting note: this needed the `Complex.conj_ofReal` instead of `IsROrC.conj_ofReal`;
  -- I believe this is because the respective coercions are no longer defeq, and
  -- `Real.Angle.coe_expMapCircle` uses the `Complex` version.
  simp only [o.rotation_apply, map_add, map_mul, LinearMap.map_smulₛₗ, RingHom.id_apply,
    LinearMap.add_apply, LinearMap.smul_apply, real_smul, kahler_rightAngleRotation_left,
    Real.Angle.coe_expMapCircle, Complex.conj_ofReal, conj_I]
  ring
  -- 🎉 no goals
#align orientation.kahler_rotation_left Orientation.kahler_rotation_left

/-- Negating a rotation is equivalent to rotation by π plus the angle. -/
theorem neg_rotation (θ : Real.Angle) (x : V) : -o.rotation θ x = o.rotation (π + θ) x := by
  rw [← o.rotation_pi_apply, rotation_rotation]
  -- 🎉 no goals
#align orientation.neg_rotation Orientation.neg_rotation

/-- Negating a rotation by -π / 2 is equivalent to rotation by π / 2. -/
@[simp]
theorem neg_rotation_neg_pi_div_two (x : V) :
    -o.rotation (-π / 2 : ℝ) x = o.rotation (π / 2 : ℝ) x := by
  rw [neg_rotation, ← Real.Angle.coe_add, neg_div, ← sub_eq_add_neg, sub_half]
  -- 🎉 no goals
#align orientation.neg_rotation_neg_pi_div_two Orientation.neg_rotation_neg_pi_div_two

/-- Negating a rotation by π / 2 is equivalent to rotation by -π / 2. -/
theorem neg_rotation_pi_div_two (x : V) : -o.rotation (π / 2 : ℝ) x = o.rotation (-π / 2 : ℝ) x :=
  (neg_eq_iff_eq_neg.mp <| o.neg_rotation_neg_pi_div_two _).symm
#align orientation.neg_rotation_pi_div_two Orientation.neg_rotation_pi_div_two

/-- Rotating the first of two vectors by `θ` scales their Kahler form by `cos (-θ) + sin (-θ) * I`.
-/
theorem kahler_rotation_left' (x y : V) (θ : Real.Angle) :
    o.kahler (o.rotation θ x) y = (-θ).expMapCircle * o.kahler x y := by
  simp only [Real.Angle.expMapCircle_neg, coe_inv_circle_eq_conj, kahler_rotation_left]
  -- 🎉 no goals
#align orientation.kahler_rotation_left' Orientation.kahler_rotation_left'

/-- Rotating the second of two vectors by `θ` scales their Kahler form by `cos θ + sin θ * I`. -/
@[simp]
theorem kahler_rotation_right (x y : V) (θ : Real.Angle) :
    o.kahler x (o.rotation θ y) = θ.expMapCircle * o.kahler x y := by
  simp only [o.rotation_apply, map_add, LinearMap.map_smulₛₗ, RingHom.id_apply, real_smul,
    kahler_rightAngleRotation_right, Real.Angle.coe_expMapCircle]
  ring
  -- 🎉 no goals
#align orientation.kahler_rotation_right Orientation.kahler_rotation_right

/-- Rotating the first vector by `θ` subtracts `θ` from the angle between two vectors. -/
@[simp]
theorem oangle_rotation_left {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) y = o.oangle x y - θ := by
  simp only [oangle, o.kahler_rotation_left']
  -- ⊢ ↑(arg (↑(Real.Angle.expMapCircle (-θ)) * ↑(↑(kahler o) x) y)) = ↑(arg (↑(↑(k …
  rw [Complex.arg_mul_coe_angle, Real.Angle.arg_expMapCircle]
  · abel
    -- 🎉 no goals
    -- 🎉 no goals
  · exact ne_zero_of_mem_circle _
    -- 🎉 no goals
  · exact o.kahler_ne_zero hx hy
    -- 🎉 no goals
#align orientation.oangle_rotation_left Orientation.oangle_rotation_left

/-- Rotating the second vector by `θ` adds `θ` to the angle between two vectors. -/
@[simp]
theorem oangle_rotation_right {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (θ : Real.Angle) :
    o.oangle x (o.rotation θ y) = o.oangle x y + θ := by
  simp only [oangle, o.kahler_rotation_right]
  -- ⊢ ↑(arg (↑(Real.Angle.expMapCircle θ) * ↑(↑(kahler o) x) y)) = ↑(arg (↑(↑(kahl …
  rw [Complex.arg_mul_coe_angle, Real.Angle.arg_expMapCircle]
  · abel
    -- 🎉 no goals
    -- 🎉 no goals
  · exact ne_zero_of_mem_circle _
    -- 🎉 no goals
  · exact o.kahler_ne_zero hx hy
    -- 🎉 no goals
#align orientation.oangle_rotation_right Orientation.oangle_rotation_right

/-- The rotation of a vector by `θ` has an angle of `-θ` from that vector. -/
@[simp]
theorem oangle_rotation_self_left {x : V} (hx : x ≠ 0) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) x = -θ := by simp [hx]
                                           -- 🎉 no goals
#align orientation.oangle_rotation_self_left Orientation.oangle_rotation_self_left

/-- A vector has an angle of `θ` from the rotation of that vector by `θ`. -/
@[simp]
theorem oangle_rotation_self_right {x : V} (hx : x ≠ 0) (θ : Real.Angle) :
    o.oangle x (o.rotation θ x) = θ := by simp [hx]
                                          -- 🎉 no goals
#align orientation.oangle_rotation_self_right Orientation.oangle_rotation_self_right

/-- Rotating the first vector by the angle between the two vectors results in an angle of 0. -/
@[simp]
theorem oangle_rotation_oangle_left (x y : V) : o.oangle (o.rotation (o.oangle x y) x) y = 0 := by
  by_cases hx : x = 0
  -- ⊢ oangle o (↑(rotation o (oangle o x y)) x) y = 0
  · simp [hx]
    -- 🎉 no goals
  · by_cases hy : y = 0
    -- ⊢ oangle o (↑(rotation o (oangle o x y)) x) y = 0
    · simp [hy]
      -- 🎉 no goals
    · simp [hx, hy]
      -- 🎉 no goals
#align orientation.oangle_rotation_oangle_left Orientation.oangle_rotation_oangle_left

/-- Rotating the first vector by the angle between the two vectors and swapping the vectors
results in an angle of 0. -/
@[simp]
theorem oangle_rotation_oangle_right (x y : V) : o.oangle y (o.rotation (o.oangle x y) x) = 0 := by
  rw [oangle_rev]
  -- ⊢ -oangle o (↑(rotation o (oangle o x y)) x) y = 0
  simp
  -- 🎉 no goals
#align orientation.oangle_rotation_oangle_right Orientation.oangle_rotation_oangle_right

/-- Rotating both vectors by the same angle does not change the angle between those vectors. -/
@[simp]
theorem oangle_rotation (x y : V) (θ : Real.Angle) :
    o.oangle (o.rotation θ x) (o.rotation θ y) = o.oangle x y := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]
  -- ⊢ oangle o (↑(rotation o θ) x) (↑(rotation o θ) y) = oangle o x y
                          -- ⊢ oangle o (↑(rotation o θ) x) (↑(rotation o θ) y) = oangle o x y
                          -- ⊢ oangle o (↑(rotation o θ) x) (↑(rotation o θ) y) = oangle o x y
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
#align orientation.oangle_rotation Orientation.oangle_rotation

/-- A rotation of a nonzero vector equals that vector if and only if the angle is zero. -/
@[simp]
theorem rotation_eq_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : Real.Angle) :
    o.rotation θ x = x ↔ θ = 0 := by
  constructor
  -- ⊢ ↑(rotation o θ) x = x → θ = 0
  · intro h
    -- ⊢ θ = 0
    rw [eq_comm]
    -- ⊢ 0 = θ
    simpa [hx, h] using o.oangle_rotation_right hx hx θ
    -- 🎉 no goals
  · intro h
    -- ⊢ ↑(rotation o θ) x = x
    simp [h]
    -- 🎉 no goals
#align orientation.rotation_eq_self_iff_angle_eq_zero Orientation.rotation_eq_self_iff_angle_eq_zero

/-- A nonzero vector equals a rotation of that vector if and only if the angle is zero. -/
@[simp]
theorem eq_rotation_self_iff_angle_eq_zero {x : V} (hx : x ≠ 0) (θ : Real.Angle) :
    x = o.rotation θ x ↔ θ = 0 := by rw [← o.rotation_eq_self_iff_angle_eq_zero hx, eq_comm]
                                     -- 🎉 no goals
#align orientation.eq_rotation_self_iff_angle_eq_zero Orientation.eq_rotation_self_iff_angle_eq_zero

/-- A rotation of a vector equals that vector if and only if the vector or the angle is zero. -/
theorem rotation_eq_self_iff (x : V) (θ : Real.Angle) : o.rotation θ x = x ↔ x = 0 ∨ θ = 0 := by
  by_cases h : x = 0 <;> simp [h]
  -- ⊢ ↑(rotation o θ) x = x ↔ x = 0 ∨ θ = 0
                         -- 🎉 no goals
                         -- 🎉 no goals
#align orientation.rotation_eq_self_iff Orientation.rotation_eq_self_iff

/-- A vector equals a rotation of that vector if and only if the vector or the angle is zero. -/
theorem eq_rotation_self_iff (x : V) (θ : Real.Angle) : x = o.rotation θ x ↔ x = 0 ∨ θ = 0 := by
  rw [← rotation_eq_self_iff, eq_comm]
  -- 🎉 no goals
#align orientation.eq_rotation_self_iff Orientation.eq_rotation_self_iff

/-- Rotating a vector by the angle to another vector gives the second vector if and only if the
norms are equal. -/
@[simp]
theorem rotation_oangle_eq_iff_norm_eq (x y : V) : o.rotation (o.oangle x y) x = y ↔ ‖x‖ = ‖y‖ := by
  constructor
  -- ⊢ ↑(rotation o (oangle o x y)) x = y → ‖x‖ = ‖y‖
  · intro h
    -- ⊢ ‖x‖ = ‖y‖
    rw [← h, LinearIsometryEquiv.norm_map]
    -- 🎉 no goals
  · intro h
    -- ⊢ ↑(rotation o (oangle o x y)) x = y
    rw [o.eq_iff_oangle_eq_zero_of_norm_eq] <;> simp [h]
    -- ⊢ oangle o (↑(rotation o (oangle o x y)) x) y = 0
                                                -- 🎉 no goals
                                                -- 🎉 no goals
#align orientation.rotation_oangle_eq_iff_norm_eq Orientation.rotation_oangle_eq_iff_norm_eq

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by the ratio of the norms. -/
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (θ : Real.Angle) : o.oangle x y = θ ↔ y = (‖y‖ / ‖x‖) • o.rotation θ x := by
  have hp := div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx)
  -- ⊢ oangle o x y = θ ↔ y = (‖y‖ / ‖x‖) • ↑(rotation o θ) x
  constructor
  -- ⊢ oangle o x y = θ → y = (‖y‖ / ‖x‖) • ↑(rotation o θ) x
  · rintro rfl
    -- ⊢ y = (‖y‖ / ‖x‖) • ↑(rotation o (oangle o x y)) x
    rw [← LinearIsometryEquiv.map_smul, ← o.oangle_smul_left_of_pos x y hp, eq_comm,
      rotation_oangle_eq_iff_norm_eq, norm_smul, Real.norm_of_nonneg hp.le,
      div_mul_cancel _ (norm_ne_zero_iff.2 hx)]
  · intro hye
    -- ⊢ oangle o x y = θ
    rw [hye, o.oangle_smul_right_of_pos _ _ hp, o.oangle_rotation_self_right hx]
    -- 🎉 no goals
#align orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero Orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero

/-- The angle between two nonzero vectors is `θ` if and only if the second vector is the first
rotated by `θ` and scaled by a positive real. -/
theorem oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero {x y : V} (hx : x ≠ 0) (hy : y ≠ 0)
    (θ : Real.Angle) : o.oangle x y = θ ↔ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x := by
  constructor
  -- ⊢ oangle o x y = θ → ∃ r, 0 < r ∧ y = r • ↑(rotation o θ) x
  · intro h
    -- ⊢ ∃ r, 0 < r ∧ y = r • ↑(rotation o θ) x
    rw [o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy] at h
    -- ⊢ ∃ r, 0 < r ∧ y = r • ↑(rotation o θ) x
    exact ⟨‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy) (norm_pos_iff.2 hx), h⟩
    -- 🎉 no goals
  · rintro ⟨r, hr, rfl⟩
    -- ⊢ oangle o x (r • ↑(rotation o θ) x) = θ
    rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right hx]
    -- 🎉 no goals
#align orientation.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero Orientation.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by the ratio of the norms, or `θ` and at least one of the
vectors are zero. -/
theorem oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
    o.oangle x y = θ ↔
      x ≠ 0 ∧ y ≠ 0 ∧ y = (‖y‖ / ‖x‖) • o.rotation θ x ∨ θ = 0 ∧ (x = 0 ∨ y = 0) := by
  by_cases hx : x = 0
  -- ⊢ oangle o x y = θ ↔ x ≠ 0 ∧ y ≠ 0 ∧ y = (‖y‖ / ‖x‖) • ↑(rotation o θ) x ∨ θ = …
  · simp [hx, eq_comm]
    -- 🎉 no goals
  · by_cases hy : y = 0
    -- ⊢ oangle o x y = θ ↔ x ≠ 0 ∧ y ≠ 0 ∧ y = (‖y‖ / ‖x‖) • ↑(rotation o θ) x ∨ θ = …
    · simp [hy, eq_comm]
      -- 🎉 no goals
    · rw [o.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero hx hy]
      -- ⊢ y = (‖y‖ / ‖x‖) • ↑(rotation o θ) x ↔ x ≠ 0 ∧ y ≠ 0 ∧ y = (‖y‖ / ‖x‖) • ↑(ro …
      simp [hx, hy]
      -- 🎉 no goals
#align orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero Orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_or_eq_zero

/-- The angle between two vectors is `θ` if and only if they are nonzero and the second vector
is the first rotated by `θ` and scaled by a positive real, or `θ` and at least one of the
vectors are zero. -/
theorem oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero {x y : V} (θ : Real.Angle) :
    o.oangle x y = θ ↔
      (x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • o.rotation θ x) ∨ θ = 0 ∧ (x = 0 ∨ y = 0) := by
  by_cases hx : x = 0
  -- ⊢ oangle o x y = θ ↔ (x ≠ 0 ∧ y ≠ 0 ∧ ∃ r, 0 < r ∧ y = r • ↑(rotation o θ) x)  …
  · simp [hx, eq_comm]
    -- 🎉 no goals
  · by_cases hy : y = 0
    -- ⊢ oangle o x y = θ ↔ (x ≠ 0 ∧ y ≠ 0 ∧ ∃ r, 0 < r ∧ y = r • ↑(rotation o θ) x)  …
    · simp [hy, eq_comm]
      -- 🎉 no goals
    · rw [o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero hx hy]
      -- ⊢ (∃ r, 0 < r ∧ y = r • ↑(rotation o θ) x) ↔ (x ≠ 0 ∧ y ≠ 0 ∧ ∃ r, 0 < r ∧ y = …
      simp [hx, hy]
      -- 🎉 no goals
#align orientation.oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero Orientation.oangle_eq_iff_eq_pos_smul_rotation_or_eq_zero

/-- Any linear isometric equivalence in `V` with positive determinant is `rotation`. -/
theorem exists_linearIsometryEquiv_eq_of_det_pos {f : V ≃ₗᵢ[ℝ] V}
    (hd : 0 < LinearMap.det (f.toLinearEquiv : V →ₗ[ℝ] V)) :
    ∃ θ : Real.Angle, f = o.rotation θ := by
  haveI : Nontrivial V :=
    FiniteDimensional.nontrivial_of_finrank_eq_succ (@Fact.out (finrank ℝ V = 2) _)
  obtain ⟨x, hx⟩ : ∃ x, x ≠ (0 : V) := exists_ne (0 : V)
  -- ⊢ ∃ θ, f = rotation o θ
  use o.oangle x (f x)
  -- ⊢ f = rotation o (oangle o x (↑f x))
  apply LinearIsometryEquiv.toLinearEquiv_injective
  -- ⊢ f.toLinearEquiv = (rotation o (oangle o x (↑f x))).toLinearEquiv
  apply LinearEquiv.toLinearMap_injective
  -- ⊢ ↑f.toLinearEquiv = ↑(rotation o (oangle o x (↑f x))).toLinearEquiv
  apply (o.basisRightAngleRotation x hx).ext
  -- ⊢ ∀ (i : Fin 2), ↑↑f.toLinearEquiv (↑(basisRightAngleRotation o x hx) i) = ↑↑( …
  intro i
  -- ⊢ ↑↑f.toLinearEquiv (↑(basisRightAngleRotation o x hx) i) = ↑↑(rotation o (oan …
  symm
  -- ⊢ ↑↑(rotation o (oangle o x (↑f x))).toLinearEquiv (↑(basisRightAngleRotation  …
  fin_cases i
  -- ⊢ ↑↑(rotation o (oangle o x (↑f x))).toLinearEquiv (↑(basisRightAngleRotation  …
  · simp
    -- 🎉 no goals
  have : o.oangle (J x) (f (J x)) = o.oangle x (f x) := by
    simp only [oangle, o.linearIsometryEquiv_comp_rightAngleRotation f hd,
      o.kahler_comp_rightAngleRotation]
  simp [← this]
  -- 🎉 no goals
#align orientation.exists_linear_isometry_equiv_eq_of_det_pos Orientation.exists_linearIsometryEquiv_eq_of_det_pos

theorem rotation_map (θ : Real.Angle) (f : V ≃ₗᵢ[ℝ] V') (x : V') :
    (Orientation.map (Fin 2) f.toLinearEquiv o).rotation θ x = f (o.rotation θ (f.symm x)) := by
  simp [rotation_apply, o.rightAngleRotation_map]
  -- 🎉 no goals
#align orientation.rotation_map Orientation.rotation_map

@[simp]
protected theorem _root_.Complex.rotation (θ : Real.Angle) (z : ℂ) :
    Complex.orientation.rotation θ z = θ.expMapCircle * z := by
  simp only [rotation_apply, Complex.rightAngleRotation, Real.Angle.coe_expMapCircle, real_smul]
  -- ⊢ ↑(Real.Angle.cos θ) * z + ↑(Real.Angle.sin θ) * (I * z) = (↑(Real.Angle.cos  …
  ring
  -- 🎉 no goals
#align complex.rotation Complex.rotation

/-- Rotation in an oriented real inner product space of dimension 2 can be evaluated in terms of a
complex-number representation of the space. -/
theorem rotation_map_complex (θ : Real.Angle) (f : V ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x : V) :
    f (o.rotation θ x) = θ.expMapCircle * f x := by
  rw [← Complex.rotation, ← hf, o.rotation_map, LinearIsometryEquiv.symm_apply_apply]
  -- 🎉 no goals
#align orientation.rotation_map_complex Orientation.rotation_map_complex

/-- Negating the orientation negates the angle in `rotation`. -/
theorem rotation_neg_orientation_eq_neg (θ : Real.Angle) : (-o).rotation θ = o.rotation (-θ) :=
  LinearIsometryEquiv.ext <| by simp [rotation_apply]
                                -- 🎉 no goals
#align orientation.rotation_neg_orientation_eq_neg Orientation.rotation_neg_orientation_eq_neg

/-- The inner product between a `π / 2` rotation of a vector and that vector is zero. -/
@[simp]
theorem inner_rotation_pi_div_two_left (x : V) : ⟪o.rotation (π / 2 : ℝ) x, x⟫ = 0 := by
  rw [rotation_pi_div_two, inner_rightAngleRotation_self]
  -- 🎉 no goals
#align orientation.inner_rotation_pi_div_two_left Orientation.inner_rotation_pi_div_two_left

/-- The inner product between a vector and a `π / 2` rotation of that vector is zero. -/
@[simp]
theorem inner_rotation_pi_div_two_right (x : V) : ⟪x, o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_rotation_pi_div_two_left]
  -- 🎉 no goals
#align orientation.inner_rotation_pi_div_two_right Orientation.inner_rotation_pi_div_two_right

/-- The inner product between a multiple of a `π / 2` rotation of a vector and that vector is
zero. -/
@[simp]
theorem inner_smul_rotation_pi_div_two_left (x : V) (r : ℝ) :
    ⟪r • o.rotation (π / 2 : ℝ) x, x⟫ = 0 := by
  rw [inner_smul_left, inner_rotation_pi_div_two_left, mul_zero]
  -- 🎉 no goals
#align orientation.inner_smul_rotation_pi_div_two_left Orientation.inner_smul_rotation_pi_div_two_left

/-- The inner product between a vector and a multiple of a `π / 2` rotation of that vector is
zero. -/
@[simp]
theorem inner_smul_rotation_pi_div_two_right (x : V) (r : ℝ) :
    ⟪x, r • o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_smul_rotation_pi_div_two_left]
  -- 🎉 no goals
#align orientation.inner_smul_rotation_pi_div_two_right Orientation.inner_smul_rotation_pi_div_two_right

/-- The inner product between a `π / 2` rotation of a vector and a multiple of that vector is
zero. -/
@[simp]
theorem inner_rotation_pi_div_two_left_smul (x : V) (r : ℝ) :
    ⟪o.rotation (π / 2 : ℝ) x, r • x⟫ = 0 := by
  rw [inner_smul_right, inner_rotation_pi_div_two_left, mul_zero]
  -- 🎉 no goals
#align orientation.inner_rotation_pi_div_two_left_smul Orientation.inner_rotation_pi_div_two_left_smul

/-- The inner product between a multiple of a vector and a `π / 2` rotation of that vector is
zero. -/
@[simp]
theorem inner_rotation_pi_div_two_right_smul (x : V) (r : ℝ) :
    ⟪r • x, o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_rotation_pi_div_two_left_smul]
  -- 🎉 no goals
#align orientation.inner_rotation_pi_div_two_right_smul Orientation.inner_rotation_pi_div_two_right_smul

/-- The inner product between a multiple of a `π / 2` rotation of a vector and a multiple of
that vector is zero. -/
@[simp]
theorem inner_smul_rotation_pi_div_two_smul_left (x : V) (r₁ r₂ : ℝ) :
    ⟪r₁ • o.rotation (π / 2 : ℝ) x, r₂ • x⟫ = 0 := by
  rw [inner_smul_right, inner_smul_rotation_pi_div_two_left, mul_zero]
  -- 🎉 no goals
#align orientation.inner_smul_rotation_pi_div_two_smul_left Orientation.inner_smul_rotation_pi_div_two_smul_left

/-- The inner product between a multiple of a vector and a multiple of a `π / 2` rotation of
that vector is zero. -/
@[simp]
theorem inner_smul_rotation_pi_div_two_smul_right (x : V) (r₁ r₂ : ℝ) :
    ⟪r₂ • x, r₁ • o.rotation (π / 2 : ℝ) x⟫ = 0 := by
  rw [real_inner_comm, inner_smul_rotation_pi_div_two_smul_left]
  -- 🎉 no goals
#align orientation.inner_smul_rotation_pi_div_two_smul_right Orientation.inner_smul_rotation_pi_div_two_smul_right

/-- The inner product between two vectors is zero if and only if the first vector is zero or
the second is a multiple of a `π / 2` rotation of that vector. -/
theorem inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two {x y : V} :
    ⟪x, y⟫ = 0 ↔ x = 0 ∨ ∃ r : ℝ, r • o.rotation (π / 2 : ℝ) x = y := by
  rw [← o.eq_zero_or_oangle_eq_iff_inner_eq_zero]
  -- ⊢ x = 0 ∨ y = 0 ∨ oangle o x y = ↑(π / 2) ∨ oangle o x y = ↑(-π / 2) ↔ x = 0 ∨ …
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ x = 0 ∨ ∃ r, r • ↑(rotation o ↑(π / 2)) x = y
  · rcases h with (rfl | rfl | h | h)
    · exact Or.inl rfl
      -- 🎉 no goals
    · exact Or.inr ⟨0, zero_smul _ _⟩
      -- 🎉 no goals
    · obtain ⟨r, _, rfl⟩ :=
        (o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero (o.left_ne_zero_of_oangle_eq_pi_div_two h)
          (o.right_ne_zero_of_oangle_eq_pi_div_two h) _).1 h
      exact Or.inr ⟨r, rfl⟩
      -- 🎉 no goals
    · obtain ⟨r, _, rfl⟩ :=
        (o.oangle_eq_iff_eq_pos_smul_rotation_of_ne_zero
          (o.left_ne_zero_of_oangle_eq_neg_pi_div_two h)
          (o.right_ne_zero_of_oangle_eq_neg_pi_div_two h) _).1 h
      refine' Or.inr ⟨-r, _⟩
      -- ⊢ -r • ↑(rotation o ↑(π / 2)) x = r • ↑(rotation o ↑(-π / 2)) x
      rw [neg_smul, ← smul_neg, o.neg_rotation_pi_div_two]
      -- 🎉 no goals
  · rcases h with (rfl | ⟨r, rfl⟩)
    -- ⊢ 0 = 0 ∨ y = 0 ∨ oangle o 0 y = ↑(π / 2) ∨ oangle o 0 y = ↑(-π / 2)
    · exact Or.inl rfl
      -- 🎉 no goals
    · by_cases hx : x = 0; · exact Or.inl hx
      -- ⊢ x = 0 ∨ r • ↑(rotation o ↑(π / 2)) x = 0 ∨ oangle o x (r • ↑(rotation o ↑(π  …
                             -- 🎉 no goals
      rcases lt_trichotomy r 0 with (hr | rfl | hr)
      · refine' Or.inr (Or.inr (Or.inr _))
        -- ⊢ oangle o x (r • ↑(rotation o ↑(π / 2)) x) = ↑(-π / 2)
        rw [o.oangle_smul_right_of_neg _ _ hr, o.neg_rotation_pi_div_two,
          o.oangle_rotation_self_right hx]
      · exact Or.inr (Or.inl (zero_smul _ _))
        -- 🎉 no goals
      · refine' Or.inr (Or.inr (Or.inl _))
        -- ⊢ oangle o x (r • ↑(rotation o ↑(π / 2)) x) = ↑(π / 2)
        rw [o.oangle_smul_right_of_pos _ _ hr, o.oangle_rotation_self_right hx]
        -- 🎉 no goals
#align orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two Orientation.inner_eq_zero_iff_eq_zero_or_eq_smul_rotation_pi_div_two

end Orientation
