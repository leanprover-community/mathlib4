/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François Sunatori
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Isometries of the Complex Plane

The lemma `linear_isometry_complex` states the classification of isometries in the complex plane.
Specifically, isometries with rotations but without translation.
The proof involves:
1. creating a linear isometry `g` with two fixed points, `g(0) = 0`, `g(1) = 1`
2. applying `linear_isometry_complex_aux` to `g`
The proof of `linear_isometry_complex_aux` is separated in the following parts:
1. show that the real parts match up: `LinearIsometry.re_apply_eq_re`
2. show that I maps to either I or -I
3. every z is a linear combination of a + b * I

## References

* [Isometries of the Complex Plane](http://helmut.knaust.info/mediawiki/images/b/b5/Iso.pdf)
-/


noncomputable section

open Complex

open CharZero

open ComplexConjugate

local notation "|" x "|" => Complex.abs x

/-- An element of the unit circle defines a `LinearIsometryEquiv` from `ℂ` to itself, by
rotation. -/
def rotation : Circle →* ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun a :=
    { DistribMulAction.toLinearEquiv ℝ ℂ a with
      norm_map' x := show ‖a * x‖ = ‖x‖ by
        rw [norm_mul, Circle.norm_coe, one_mul] }
  map_one' := LinearIsometryEquiv.ext <| by simp
  map_mul' a b := LinearIsometryEquiv.ext <| mul_smul a b

@[simp]
theorem rotation_apply (a : Circle) (z : ℂ) : rotation a z = a * z :=
  rfl

@[simp]
theorem rotation_symm (a : Circle) : (rotation a).symm = rotation a⁻¹ :=
  LinearIsometryEquiv.ext fun _ => rfl

@[simp]
theorem rotation_trans (a b : Circle) : (rotation a).trans (rotation b) = rotation (b * a) := by
  ext1
  simp

theorem rotation_ne_conjLIE (a : Circle) : rotation a ≠ conjLIE := by
  intro h
  have h1 : rotation a 1 = conj 1 := LinearIsometryEquiv.congr_fun h 1
  have hI : rotation a I = conj I := LinearIsometryEquiv.congr_fun h I
  rw [rotation_apply, RingHom.map_one, mul_one] at h1
  rw [rotation_apply, conj_I, ← neg_one_mul, mul_left_inj' I_ne_zero, h1, eq_neg_self_iff] at hI
  exact one_ne_zero hI

/-- Takes an element of `ℂ ≃ₗᵢ[ℝ] ℂ` and checks if it is a rotation, returns an element of the
unit circle. -/
@[simps]
def rotationOf (e : ℂ ≃ₗᵢ[ℝ] ℂ) : Circle :=
  ⟨e 1 / ‖e 1‖, by simp [Submonoid.unitSphere]⟩

@[simp]
theorem rotationOf_rotation (a : Circle) : rotationOf (rotation a) = a :=
  Subtype.ext <| by simp

theorem rotation_injective : Function.Injective rotation :=
  Function.LeftInverse.injective rotationOf_rotation

theorem LinearIsometry.re_apply_eq_re_of_add_conj_eq (f : ℂ →ₗᵢ[ℝ] ℂ)
    (h₃ : ∀ z, z + conj z = f z + conj (f z)) (z : ℂ) : (f z).re = z.re := by
  simpa [Complex.ext_iff, add_re, add_im, conj_re, conj_im, ← two_mul,
    show (2 : ℝ) ≠ 0 by simp] using (h₃ z).symm

theorem LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ}
    (h₂ : ∀ z, (f z).re = z.re) (z : ℂ) : (f z).im = z.im ∨ (f z).im = -z.im := by
  have h₁ := f.norm_map z
  simp only [norm_def] at h₁
  rwa [Real.sqrt_inj (normSq_nonneg _) (normSq_nonneg _), normSq_apply (f z), normSq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁

theorem LinearIsometry.im_apply_eq_im {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) :
    z + conj z = f z + conj (f z) := by
  have : ‖f z - 1‖ = ‖z - 1‖ := by rw [← f.norm_map (z - 1), f.map_sub, h]
  apply_fun fun x => x ^ 2 at this
  simp only [← normSq_eq_norm_sq] at this
  rw [← ofReal_inj, ← mul_conj, ← mul_conj] at this
  rw [RingHom.map_sub, RingHom.map_sub] at this
  simp only [sub_mul, mul_sub, one_mul] at this
  rw [mul_conj, normSq_eq_norm_sq, LinearIsometry.norm_map] at this
  rw [mul_conj, normSq_eq_norm_sq] at this
  simp only [sub_sub, sub_right_inj, mul_one, ofReal_pow, RingHom.map_one] at this
  simp only [add_sub, sub_left_inj] at this
  rw [add_comm, ← this, add_comm]

theorem LinearIsometry.re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : (f z).re = z.re := by
  apply LinearIsometry.re_apply_eq_re_of_add_conj_eq
  intro z
  apply LinearIsometry.im_apply_eq_im h

theorem linear_isometry_complex_aux {f : ℂ ≃ₗᵢ[ℝ] ℂ} (h : f 1 = 1) :
    f = LinearIsometryEquiv.refl ℝ ℂ ∨ f = conjLIE := by
  have h0 : f I = I ∨ f I = -I := by
    simp only [Complex.ext_iff, ← and_or_left, neg_re, I_re, neg_im, neg_zero]
    constructor
    · rw [← I_re]
      exact @LinearIsometry.re_apply_eq_re f.toLinearIsometry h I
    · apply @LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.toLinearIsometry
      intro z
      rw [@LinearIsometry.re_apply_eq_re f.toLinearIsometry h]
  refine h0.imp (fun h' : f I = I => ?_) fun h' : f I = -I => ?_ <;>
    · apply LinearIsometryEquiv.toLinearEquiv_injective
      apply Complex.basisOneI.ext'
      intro i
      fin_cases i <;> simp [h, h']

theorem linear_isometry_complex (f : ℂ ≃ₗᵢ[ℝ] ℂ) :
    ∃ a : Circle, f = rotation a ∨ f = conjLIE.trans (rotation a) := by
  let a : Circle := ⟨f 1, by simp [Submonoid.unitSphere, f.norm_map]⟩
  use a
  have : (f.trans (rotation a).symm) 1 = 1 := by simpa [a] using rotation_apply a⁻¹ (f 1)
  refine (linear_isometry_complex_aux this).imp (fun h₁ => ?_) fun h₂ => ?_
  · simpa using eq_mul_of_inv_mul_eq h₁
  · exact eq_mul_of_inv_mul_eq h₂

/-- The matrix representation of `rotation a` is equal to the conformal matrix
`!![re a, -im a; im a, re a]`. -/
theorem toMatrix_rotation (a : Circle) :
    LinearMap.toMatrix basisOneI basisOneI (rotation a).toLinearEquiv =
      Matrix.planeConformalMatrix (re a) (im a) (by simp [pow_two, ← normSq_apply]) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, coe_basisOneI, LinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toLinearEquiv, rotation_apply, coe_basisOneI_repr, mul_re, mul_im,
    Matrix.val_planeConformalMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one]
  fin_cases i <;> fin_cases j <;> simp

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp]
theorem det_rotation (a : Circle) : LinearMap.det ((rotation a).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = 1 := by
  rw [← LinearMap.det_toMatrix basisOneI, toMatrix_rotation, Matrix.det_fin_two]
  simp [← normSq_apply]

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp]
theorem linearEquiv_det_rotation (a : Circle) : LinearEquiv.det (rotation a).toLinearEquiv = 1 := by
  rw [← Units.val_inj, LinearEquiv.coe_det, det_rotation, Units.val_one]
