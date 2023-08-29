/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: François Sunatori
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup

#align_import analysis.complex.isometry from "leanprover-community/mathlib"@"ae690b0c236e488a0043f6faa8ce3546e7f2f9c5"

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

open ComplexConjugate

local notation "|" x "|" => Complex.abs x

/-- An element of the unit circle defines a `LinearIsometryEquiv` from `ℂ` to itself, by
rotation. -/
def rotation : circle →* ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun a :=
    { DistribMulAction.toLinearEquiv ℝ ℂ a with
      norm_map' := fun x => show |a * x| = |x| by rw [map_mul, abs_coe_circle, one_mul] }
                                                  -- 🎉 no goals
  map_one' := LinearIsometryEquiv.ext <| one_smul circle
  map_mul' a b := LinearIsometryEquiv.ext <| mul_smul a b
#align rotation rotation

@[simp]
theorem rotation_apply (a : circle) (z : ℂ) : rotation a z = a * z :=
  rfl
#align rotation_apply rotation_apply

@[simp]
theorem rotation_symm (a : circle) : (rotation a).symm = rotation a⁻¹ :=
  LinearIsometryEquiv.ext fun _ => rfl
#align rotation_symm rotation_symm

@[simp]
theorem rotation_trans (a b : circle) : (rotation a).trans (rotation b) = rotation (b * a) := by
  ext1
  -- ⊢ ↑(LinearIsometryEquiv.trans (↑rotation a) (↑rotation b)) x✝ = ↑(↑rotation (b …
  simp
  -- 🎉 no goals
#align rotation_trans rotation_trans

theorem rotation_ne_conjLie (a : circle) : rotation a ≠ conjLie := by
  intro h
  -- ⊢ False
  have h1 : rotation a 1 = conj 1 := LinearIsometryEquiv.congr_fun h 1
  -- ⊢ False
  have hI : rotation a I = conj I := LinearIsometryEquiv.congr_fun h I
  -- ⊢ False
  rw [rotation_apply, RingHom.map_one, mul_one] at h1
  -- ⊢ False
  rw [rotation_apply, conj_I, ← neg_one_mul, mul_left_inj' I_ne_zero, h1, eq_neg_self_iff] at hI
  -- ⊢ False
  exact one_ne_zero hI
  -- 🎉 no goals
#align rotation_ne_conj_lie rotation_ne_conjLie

/-- Takes an element of `ℂ ≃ₗᵢ[ℝ] ℂ` and checks if it is a rotation, returns an element of the
unit circle. -/
@[simps]
def rotationOf (e : ℂ ≃ₗᵢ[ℝ] ℂ) : circle :=
  ⟨e 1 / Complex.abs (e 1), by simp⟩
                               -- 🎉 no goals
#align rotation_of rotationOf

@[simp]
theorem rotationOf_rotation (a : circle) : rotationOf (rotation a) = a :=
  Subtype.ext <| by simp
                    -- 🎉 no goals
#align rotation_of_rotation rotationOf_rotation

theorem rotation_injective : Function.Injective rotation :=
  Function.LeftInverse.injective rotationOf_rotation
#align rotation_injective rotation_injective

theorem LinearIsometry.re_apply_eq_re_of_add_conj_eq (f : ℂ →ₗᵢ[ℝ] ℂ)
    (h₃ : ∀ z, z + conj z = f z + conj (f z)) (z : ℂ) : (f z).re = z.re := by
  simpa [ext_iff, add_re, add_im, conj_re, conj_im, ← two_mul,
    show (2 : ℝ) ≠ 0 by simp [two_ne_zero]] using (h₃ z).symm
#align linear_isometry.re_apply_eq_re_of_add_conj_eq LinearIsometry.re_apply_eq_re_of_add_conj_eq

theorem LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ}
    (h₂ : ∀ z, (f z).re = z.re) (z : ℂ) : (f z).im = z.im ∨ (f z).im = -z.im := by
  have h₁ := f.norm_map z
  -- ⊢ (↑f z).im = z.im ∨ (↑f z).im = -z.im
  simp only [Complex.abs_def, norm_eq_abs] at h₁
  -- ⊢ (↑f z).im = z.im ∨ (↑f z).im = -z.im
  rwa [Real.sqrt_inj (normSq_nonneg _) (normSq_nonneg _), normSq_apply (f z), normSq_apply z,
    h₂, add_left_cancel_iff, mul_self_eq_mul_self_iff] at h₁
#align linear_isometry.im_apply_eq_im_or_neg_of_re_apply_eq_re LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re

theorem LinearIsometry.im_apply_eq_im {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) :
    z + conj z = f z + conj (f z) := by
  have : ‖f z - 1‖ = ‖z - 1‖ := by rw [← f.norm_map (z - 1), f.map_sub, h]
  -- ⊢ z + ↑(starRingEnd ℂ) z = ↑f z + ↑(starRingEnd ((fun x => ℂ) z)) (↑f z)
  apply_fun fun x => x ^ 2 at this
  -- ⊢ z + ↑(starRingEnd ℂ) z = ↑f z + ↑(starRingEnd ((fun x => ℂ) z)) (↑f z)
  simp only [norm_eq_abs, ← normSq_eq_abs] at this
  -- ⊢ z + ↑(starRingEnd ℂ) z = ↑f z + ↑(starRingEnd ((fun x => ℂ) z)) (↑f z)
  rw [← ofReal_inj, ← mul_conj, ← mul_conj] at this
  -- ⊢ z + ↑(starRingEnd ℂ) z = ↑f z + ↑(starRingEnd ((fun x => ℂ) z)) (↑f z)
  rw [RingHom.map_sub, RingHom.map_sub] at this
  -- ⊢ z + ↑(starRingEnd ℂ) z = ↑f z + ↑(starRingEnd ((fun x => ℂ) z)) (↑f z)
  simp only [sub_mul, mul_sub, one_mul, mul_one] at this
  -- ⊢ z + ↑(starRingEnd ℂ) z = ↑f z + ↑(starRingEnd ((fun x => ℂ) z)) (↑f z)
  rw [mul_conj, normSq_eq_abs, ← norm_eq_abs, LinearIsometry.norm_map] at this
  -- ⊢ z + ↑(starRingEnd ℂ) z = ↑f z + ↑(starRingEnd ((fun x => ℂ) z)) (↑f z)
  rw [mul_conj, normSq_eq_abs, ← norm_eq_abs] at this
  -- ⊢ z + ↑(starRingEnd ℂ) z = ↑f z + ↑(starRingEnd ((fun x => ℂ) z)) (↑f z)
  simp only [sub_sub, sub_right_inj, mul_one, ofReal_pow, RingHom.map_one, norm_eq_abs] at this
  -- ⊢ z + ↑(starRingEnd ℂ) z = ↑f z + ↑(starRingEnd ((fun x => ℂ) z)) (↑f z)
  simp only [add_sub, sub_left_inj] at this
  -- ⊢ z + ↑(starRingEnd ℂ) z = ↑f z + ↑(starRingEnd ((fun x => ℂ) z)) (↑f z)
  rw [add_comm, ← this, add_comm]
  -- 🎉 no goals
#align linear_isometry.im_apply_eq_im LinearIsometry.im_apply_eq_im

theorem LinearIsometry.re_apply_eq_re {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) (z : ℂ) : (f z).re = z.re := by
  apply LinearIsometry.re_apply_eq_re_of_add_conj_eq
  -- ⊢ ∀ (z : ℂ), z + ↑(starRingEnd ℂ) z = ↑f z + ↑(starRingEnd ((fun x => ℂ) z)) ( …
  intro z
  -- ⊢ z + ↑(starRingEnd ℂ) z = ↑f z + ↑(starRingEnd ((fun x => ℂ) z)) (↑f z)
  apply LinearIsometry.im_apply_eq_im h
  -- 🎉 no goals
#align linear_isometry.re_apply_eq_re LinearIsometry.re_apply_eq_re

theorem linear_isometry_complex_aux {f : ℂ ≃ₗᵢ[ℝ] ℂ} (h : f 1 = 1) :
    f = LinearIsometryEquiv.refl ℝ ℂ ∨ f = conjLie := by
  have h0 : f I = I ∨ f I = -I := by
    simp only [ext_iff, ← and_or_left, neg_re, I_re, neg_im, neg_zero]
    constructor
    · rw [← I_re]
      exact @LinearIsometry.re_apply_eq_re f.toLinearIsometry h I
    · apply @LinearIsometry.im_apply_eq_im_or_neg_of_re_apply_eq_re f.toLinearIsometry
      intro z
      rw [@LinearIsometry.re_apply_eq_re f.toLinearIsometry h]
  refine' h0.imp (fun h' : f I = I => _) fun h' : f I = -I => _ <;>
  -- ⊢ f = LinearIsometryEquiv.refl ℝ ℂ
    · apply LinearIsometryEquiv.toLinearEquiv_injective
      -- ⊢ f.toLinearEquiv = (LinearIsometryEquiv.refl ℝ ℂ).toLinearEquiv
      -- ⊢ f.toLinearEquiv = conjLie.toLinearEquiv
      -- ⊢ ∀ (i : Fin 2), ↑f.toLinearEquiv (↑basisOneI i) = ↑(LinearIsometryEquiv.refl  …
      apply Complex.basisOneI.ext'
      -- ⊢ ↑f.toLinearEquiv (↑basisOneI i) = ↑(LinearIsometryEquiv.refl ℝ ℂ).toLinearEq …
      -- ⊢ ∀ (i : Fin 2), ↑f.toLinearEquiv (↑basisOneI i) = ↑conjLie.toLinearEquiv (↑ba …
      -- ⊢ ↑f.toLinearEquiv (↑basisOneI { val := 0, isLt := (_ : 0 < 2) }) = ↑(LinearIs …
                      -- 🎉 no goals
                      -- 🎉 no goals
      intro i
      -- ⊢ ↑f.toLinearEquiv (↑basisOneI i) = ↑conjLie.toLinearEquiv (↑basisOneI i)
      fin_cases i <;> simp [h, h']
      -- ⊢ ↑f.toLinearEquiv (↑basisOneI { val := 0, isLt := (_ : 0 < 2) }) = ↑conjLie.t …
                      -- 🎉 no goals
                      -- 🎉 no goals
#align linear_isometry_complex_aux linear_isometry_complex_aux

theorem linear_isometry_complex (f : ℂ ≃ₗᵢ[ℝ] ℂ) :
    ∃ a : circle, f = rotation a ∨ f = conjLie.trans (rotation a) := by
  let a : circle := ⟨f 1, by rw [mem_circle_iff_abs, ← Complex.norm_eq_abs, f.norm_map, norm_one]⟩
  -- ⊢ ∃ a, f = ↑rotation a ∨ f = LinearIsometryEquiv.trans conjLie (↑rotation a)
  use a
  -- ⊢ f = ↑rotation a ∨ f = LinearIsometryEquiv.trans conjLie (↑rotation a)
  have : (f.trans (rotation a).symm) 1 = 1 := by simpa using rotation_apply a⁻¹ (f 1)
  -- ⊢ f = ↑rotation a ∨ f = LinearIsometryEquiv.trans conjLie (↑rotation a)
  refine' (linear_isometry_complex_aux this).imp (fun h₁ => _) fun h₂ => _
  -- ⊢ f = ↑rotation a
  · simpa using eq_mul_of_inv_mul_eq h₁
    -- 🎉 no goals
  · exact eq_mul_of_inv_mul_eq h₂
    -- 🎉 no goals
#align linear_isometry_complex linear_isometry_complex

/-- The matrix representation of `rotation a` is equal to the conformal matrix
`!![re a, -im a; im a, re a]`. -/
theorem toMatrix_rotation (a : circle) :
    LinearMap.toMatrix basisOneI basisOneI (rotation a).toLinearEquiv =
      Matrix.planeConformalMatrix (re a) (im a) (by simp [pow_two, ← normSq_apply]) := by
                                                    -- 🎉 no goals
  ext i j
  -- ⊢ ↑(LinearMap.toMatrix basisOneI basisOneI) (↑(↑rotation a).toLinearEquiv) i j …
  simp [LinearMap.toMatrix_apply]
  -- ⊢ Matrix.vecCons ((↑a).re * (Matrix.vecCons 1 ![I] j).re - (↑a).im * (Matrix.v …
  fin_cases i <;> fin_cases j <;> simp
  -- ⊢ Matrix.vecCons ((↑a).re * (Matrix.vecCons 1 ![I] j).re - (↑a).im * (Matrix.v …
                  -- ⊢ Matrix.vecCons ((↑a).re * (Matrix.vecCons 1 ![I] { val := 0, isLt := (_ : 0  …
                  -- ⊢ Matrix.vecCons ((↑a).re * (Matrix.vecCons 1 ![I] { val := 0, isLt := (_ : 0  …
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align to_matrix_rotation toMatrix_rotation

/-- The determinant of `rotation` (as a linear map) is equal to `1`. -/
@[simp]
theorem det_rotation (a : circle) : LinearMap.det ((rotation a).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = 1 := by
  rw [← LinearMap.det_toMatrix basisOneI, toMatrix_rotation, Matrix.det_fin_two]
  -- ⊢ ↑(Matrix.planeConformalMatrix (↑a).re (↑a).im (_ : (↑a).re ^ 2 + (↑a).im ^ 2 …
  simp [← normSq_apply]
  -- 🎉 no goals
#align det_rotation det_rotation

/-- The determinant of `rotation` (as a linear equiv) is equal to `1`. -/
@[simp]
theorem linearEquiv_det_rotation (a : circle) : LinearEquiv.det (rotation a).toLinearEquiv = 1 := by
  rw [← Units.eq_iff, LinearEquiv.coe_det, det_rotation, Units.val_one]
  -- 🎉 no goals
#align linear_equiv_det_rotation linearEquiv_det_rotation
