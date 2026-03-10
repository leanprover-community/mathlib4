/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier transform on Schwartz functions

This file constructs the Fourier transform as a continuous linear map acting on Schwartz
functions, in `fourierTransformCLM`. It is also given as a continuous linear equiv, in
`fourierTransformCLE`.

## Main statements
* `SchwartzMap.fderivCLM_fourier_eq`: The derivative of the Fourier transform is given by the
  Fourier transform of the multiplication with `-(2 * π * Complex.I) • innerSL ℝ`.
* `SchwartzMap.lineDerivOp_fourier_eq`: The line derivative of the Fourier transform is given by the
  Fourier transform of the multiplication with `-(2 * π * Complex.I) • (inner ℝ · m)`.
* `SchwartzMap.integral_bilin_fourier_eq`: The Fourier transform is self-adjoint.
* `SchwartzMap.integral_inner_fourier_fourier`: Plancherel's theorem for Schwartz functions.

-/

@[expose] public section

open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace

noncomputable section

namespace SchwartzMap

variable
  (𝕜 : Type*) [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section definition

set_option backward.isDefEq.respectTransparency false in
/-- The Fourier transform on a real inner product space, as a continuous linear map on the
Schwartz space.

This definition is only to define the Fourier transform, use `FourierTransform.fourierCLM` instead.
-/
def fourierTransformCLM : 𝓢(V, E) →L[𝕜] 𝓢(V, E) := by
  refine mkCLM ((𝓕 : (V → E) → (V → E)) ·) ?_ ?_ ?_ ?_
  · intro f g
    simp [fourier_eq, integral_add ((fourierIntegral_convergent_iff _).mpr f.integrable)
      ((fourierIntegral_convergent_iff _).mpr g.integrable)]
  · simp [fourier_eq, smul_comm, integral_smul]
  · exact fun f ↦ contDiff_fourier (fun n _ ↦ integrable_pow_mul volume f n)
  · rintro ⟨k, n⟩
    refine ⟨Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1),
      (2 * π) ^ n * (2 * n + 2) ^ k * (Finset.range (n + 1) ×ˢ Finset.range (k + 1)).card *
        2 ^ integrablePower (volume : Measure V) *
        (∫ x : V, (1 + ‖x‖) ^ (- integrablePower (volume : Measure V) : ℝ)) * 2, by positivity,
      fun f x ↦ ?_⟩
    apply (pow_mul_norm_iteratedFDeriv_fourier_le (f.smooth ⊤)
      (fun k n _hk _hn ↦ integrable_pow_mul_iteratedFDeriv _ f k n) le_top le_top x).trans
    simp only [mul_assoc]
    gcongr
    calc
    _ ≤ ∑ _ ∈ Finset.range (n + 1) ×ˢ Finset.range (k + 1),
        2 ^ integrablePower (volume : Measure V) *
          (∫ x : V, (1 + ‖x‖) ^ (- integrablePower (volume : Measure V) : ℝ)) * 2 *
          (Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1)).sup
          (schwartzSeminormFamily 𝕜 V E) f := by
      gcongr with p
      apply (f.integral_pow_mul_iteratedFDeriv_le 𝕜 ..).trans
      simp only [mul_assoc, two_mul]
      gcongr
      · have : (0, p.2) ∈ Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ
            Finset.range (k + 1) := by simp_all
        apply Seminorm.le_def.mp (Finset.le_sup (f := fun p ↦ SchwartzMap.seminorm 𝕜 p.1 p.2) this)
      · have : (p.1 + integrablePower (volume : Measure V), p.2) ∈ Finset.range
            (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1) := by simp_all
        apply Seminorm.le_def.mp (Finset.le_sup (f := fun p ↦ SchwartzMap.seminorm 𝕜 p.1 p.2) this)
    _ = _ := by simp [mul_assoc]

instance instFourierTransform : FourierTransform 𝓢(V, E) 𝓢(V, E) where
  fourier f := fourierTransformCLM ℂ f

instance instFourierAdd : FourierAdd 𝓢(V, E) 𝓢(V, E) where
  fourier_add := ContinuousLinearMap.map_add _

instance instFourierSMul : FourierSMul 𝕜 𝓢(V, E) 𝓢(V, E) where
  fourier_smul := (fourierTransformCLM 𝕜).map_smul

instance instContinuousFourier : ContinuousFourier 𝓢(V, E) 𝓢(V, E) where
  continuous_fourier := ContinuousLinearMap.continuous _

lemma fourier_coe (f : 𝓢(V, E)) : 𝓕 f = 𝓕 (f : V → E) := rfl

@[simp]
theorem fourierTransformCLM_apply (f : 𝓢(V, E)) :
    fourierTransformCLM 𝕜 f = 𝓕 f := rfl

instance instFourierTransformInv : FourierTransformInv 𝓢(V, E) 𝓢(V, E) where
  fourierInv := (compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := V)))
      ∘L (fourierTransformCLM ℂ)

instance instFourierInvAdd : FourierInvAdd 𝓢(V, E) 𝓢(V, E) where
  fourierInv_add := ContinuousLinearMap.map_add _

instance instFourierInvSMul : FourierInvSMul 𝕜 𝓢(V, E) 𝓢(V, E) where
  fourierInv_smul := ((compCLMOfContinuousLinearEquiv 𝕜 (D := V) (E := V) (F := E)
    (LinearIsometryEquiv.neg ℝ (E := V))) ∘L (fourierTransformCLM 𝕜)).map_smul

instance instContinuousFourierInv : ContinuousFourierInv 𝓢(V, E) 𝓢(V, E) where
  continuous_fourierInv := ContinuousLinearMap.continuous _

lemma fourierInv_coe (f : 𝓢(V, E)) : 𝓕⁻ f = 𝓕⁻ (f : V → E) := by
  ext x
  exact (fourierInv_eq_fourier_neg f x).symm

lemma fourierInv_apply_eq (f : 𝓢(V, E)) :
    𝓕⁻ f = (compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := V))) (𝓕 f) := by
  rfl

variable [CompleteSpace E]

instance instFourierPair : FourierPair 𝓢(V, E) 𝓢(V, E) where
  fourierInv_fourier_eq := by
    intro f
    ext x
    rw [fourierInv_coe, fourier_coe, f.continuous.fourierInv_fourier_eq f.integrable
      (𝓕 f).integrable]

instance instFourierInvPair : FourierInvPair 𝓢(V, E) 𝓢(V, E) where
  fourier_fourierInv_eq := by
    intro f
    ext x
    rw [fourier_coe, fourierInv_coe, f.continuous.fourier_fourierInv_eq f.integrable
      (𝓕 f).integrable]

@[deprecated (since := "2025-11-13")]
alias fourier_inversion := FourierTransform.fourierInv_fourier_eq

@[deprecated (since := "2025-11-13")]
alias fourier_inversion_inv := FourierTransform.fourier_fourierInv_eq

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE := FourierTransform.fourierCLE

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE_apply := FourierTransform.fourierCLE_apply

@[deprecated (since := "2026-01-06")]
alias fourierTransformCLE_symm_apply := FourierTransform.fourierCLE_symm_apply

end definition

section eval

variable {𝕜' : Type*} [NormedField 𝕜']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace 𝕜' G] [SMulCommClass ℝ 𝕜' G]

set_option backward.isDefEq.respectTransparency false in
variable (𝕜') in
theorem fourier_evalCLM_eq (f : 𝓢(V, F →L[ℝ] G)) (m : F) :
    𝓕 (SchwartzMap.evalCLM 𝕜' V G m f) = SchwartzMap.evalCLM 𝕜' V G m (𝓕 f) := by
  ext x
  exact (fourier_continuousLinearMap_apply f.integrable).symm

end eval

section deriv

set_option backward.isDefEq.respectTransparency false

/-- The derivative of the Fourier transform is given by the Fourier transform of the multiplication
with `-(2 * π * Complex.I) • innerSL ℝ`. -/
theorem fderivCLM_fourier_eq (f : 𝓢(V, E)) :
    fderivCLM 𝕜 V E (𝓕 f) = 𝓕 (-(2 * π * Complex.I) • smulRightCLM ℂ E (innerSL ℝ) f) := by
  ext1 x
  change fderiv ℝ (𝓕 ⇑f) x = _
  calc
    _ = 𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) f) x := by
      rw [fderiv_fourier f.integrable]
      simpa using f.integrable_pow_mul volume 1

/-- The Fourier transform of the derivative is given by multiplication of
`(2 * π * Complex.I) • innerSL ℝ` with the Fourier transform. -/
theorem fourier_fderivCLM_eq (f : 𝓢(V, E)) :
    𝓕 (fderivCLM 𝕜 V E f) = (2 * π * Complex.I) • smulRightCLM ℂ E (innerSL ℝ) (𝓕 f) := by
  ext x m
  change 𝓕 (fderiv ℝ ⇑f) x m = _
  simp [fourier_fderiv f.integrable f.differentiable (fderivCLM ℝ V E f).integrable,
    innerSL_apply_apply ℝ, fourier_coe]

open LineDeriv

/- The line derivative in direction `m` of the Fourier transform is given by the Fourier transform
of the multiplication with `-(2 * π * Complex.I) • (inner ℝ · m)`. -/
theorem lineDerivOp_fourier_eq (f : 𝓢(V, E)) (m : V) :
    ∂_{m} (𝓕 f) = 𝓕 (-(2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) f) := by
  change SchwartzMap.evalCLM ℝ V E m (fderivCLM ℝ V E (𝓕 f)) = _
  rw [fderivCLM_fourier_eq, ← fourier_evalCLM_eq]
  congr
  ext
  have : (inner ℝ · m).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
  simp [this, innerSL_apply_apply ℝ]

/- The Fourier transform of line derivative in direction `m` is given by multiplication of
`(2 * π * Complex.I) • (inner ℝ · m)` with the Fourier transform. -/
theorem fourier_lineDerivOp_eq (f : 𝓢(V, E)) (m : V) :
    𝓕 (∂_{m} f) = (2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) (𝓕 f) := by
  change 𝓕 (SchwartzMap.evalCLM ℝ V E m (fderivCLM ℝ V E f)) = _
  ext
  have : (inner ℝ · m).HasTemperateGrowth := ((innerSL ℝ).flip m).hasTemperateGrowth
  simp [fourier_evalCLM_eq ℝ, fourier_fderivCLM_eq, this, innerSL_apply_apply ℝ]

/- The line derivative in direction `m` of the inverse Fourier transform is given by the inverse
Fourier transform of the multiplication with `(2 * π * Complex.I) • (inner ℝ · m)`. -/
theorem lineDerivOp_fourierInv_eq (f : 𝓢(V, E)) (m : V) :
    ∂_{m} (𝓕⁻ f) = 𝓕⁻ ((2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) f) := by
  simp [fourierInv_apply_eq, lineDerivOp_compCLMOfContinuousLinearEquiv, lineDerivOp_fourier_eq]

/- The inverse Fourier transform of line derivative in direction `m` is given by multiplication of
`-(2 * π * Complex.I) • (inner ℝ · m)` with the inverse Fourier transform. -/
theorem fourierInv_lineDerivOp_eq (f : 𝓢(V, E)) (m : V) :
    𝓕⁻ (∂_{m} f) = -(2 * π * Complex.I) • smulLeftCLM E (inner ℝ · m) (𝓕⁻ f) := by
  have : (inner ℝ · m).HasTemperateGrowth := by fun_prop
  simp [fourierInv_apply_eq, fourier_lineDerivOp_eq,
    smulLeftCLM_compCLMOfContinuousLinearEquiv ℂ this, Function.comp_def, smulLeftCLM_fun_neg this]

end deriv

section fubini

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

variable [CompleteSpace E] [CompleteSpace F]

/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint.

Version where the multiplication is replaced by a general bilinear form `M`. -/
theorem integral_bilin_fourier_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕 g x) := by
  simpa using VectorFourier.integral_bilin_fourierIntegral_eq_flip M (L := innerₗ V)
    continuous_fourierChar continuous_inner f.integrable g.integrable

@[deprecated (since := "2025-11-16")]
alias integral_bilin_fourierIntegral_eq := integral_bilin_fourier_eq

set_option backward.isDefEq.respectTransparency false in
/-- The Fourier transform satisfies `∫ 𝓕 f • g = ∫ f • 𝓕 g`, i.e., it is self-adjoint. -/
theorem integral_fourier_smul_eq (f : 𝓢(V, ℂ)) (g : 𝓢(V, F)) :
    ∫ ξ, 𝓕 f ξ • g ξ = ∫ x, f x • 𝓕 g x :=
  integral_bilin_fourier_eq f g (.lsmul ℂ ℂ)

set_option backward.isDefEq.respectTransparency false in
/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint. -/
theorem integral_fourier_mul_eq (f : 𝓢(V, ℂ)) (g : 𝓢(V, ℂ)) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x :=
  integral_bilin_fourier_eq f g (.mul ℂ ℂ)

/-- The inverse Fourier transform satisfies `∫ 𝓕⁻ f * g = ∫ f * 𝓕⁻ g`, i.e., it is self-adjoint.

Version where the multiplication is replaced by a general bilinear form `M`. -/
theorem integral_bilin_fourierInv_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕⁻ f ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g x) := by
  convert (integral_bilin_fourier_eq (𝓕⁻ f) (𝓕⁻ g) M).symm
  · exact (FourierTransform.fourier_fourierInv_eq g).symm
  · exact (FourierTransform.fourier_fourierInv_eq f).symm

set_option backward.isDefEq.respectTransparency false in
/-- The inverse Fourier transform satisfies `∫ 𝓕⁻ f • g = ∫ f • 𝓕⁻ g`, i.e., it is self-adjoint. -/
theorem integral_fourierInv_smul_eq (f : 𝓢(V, ℂ)) (g : 𝓢(V, F)) :
    ∫ ξ, 𝓕⁻ f ξ • g ξ = ∫ x, f x • 𝓕⁻ g x :=
  integral_bilin_fourierInv_eq f g (.lsmul ℂ ℂ)

set_option backward.isDefEq.respectTransparency false in
/-- The inverse Fourier transform satisfies `∫ 𝓕⁻ f * g = ∫ f * 𝓕⁻ g`, i.e., it is self-adjoint. -/
theorem integral_fourierInv_mul_eq (f : 𝓢(V, ℂ)) (g : 𝓢(V, ℂ)) :
    ∫ ξ, 𝓕⁻ f ξ * g ξ = ∫ x, f x * 𝓕⁻ g x :=
  integral_bilin_fourierInv_eq f g (.mul ℂ ℂ)

theorem integral_sesq_fourier_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L⋆[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g x) := by
  simpa [fourierInv_coe] using VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip M
    (L := innerₗ V) continuous_fourierChar continuous_inner f.integrable g.integrable

@[deprecated (since := "2025-11-16")]
alias integral_sesq_fourierIntegral_eq := integral_sesq_fourier_eq

/-- Plancherel's theorem for Schwartz functions.

Version where the inner product is replaced by a general sesquilinear form `M`. -/
theorem integral_sesq_fourier_fourier (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L⋆[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (𝓕 g ξ) = ∫ x, M (f x) (g x) := by
  simpa using integral_sesq_fourier_eq f (𝓕 g) M

end fubini

section L1

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

@[simp]
theorem norm_fourier_apply_le_toLp_one (f : 𝓢(V, F)) (x : V) :
    ‖𝓕 f x‖ ≤ ‖f.toLp 1‖ := by
  calc
    _ = ‖∫ (v : V), 𝐞 (-inner ℝ v x) • f v‖ := by rw [fourier_coe, Real.fourier_eq]
    _ ≤ ∫ (v : V), ‖𝐞 (-inner ℝ v x) • f v‖ := norm_integral_le_integral_norm _
    _ = _ := by simp [norm_toLp_one]

theorem norm_fourier_toBoundedContinuousFunction_le_toLp_one (f : 𝓢(V, F)) :
    ‖(𝓕 f).toBoundedContinuousFunction‖ ≤ ‖f.toLp 1‖ := by
  rw [BoundedContinuousFunction.norm_le (by positivity)]
  simp

theorem norm_fourier_Lp_top_leq_toLp_one (f : 𝓢(V, F)) :
    ‖(𝓕 f).toLp ⊤‖ ≤ ‖f.toLp 1‖ :=
  norm_toLp_top_le.trans (seminorm_le_bound ℝ 0 0 _ (by positivity) (fun _ ↦ by simp))

end L1

section L2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Plancherel's theorem for Schwartz functions. -/
@[simp] theorem integral_inner_fourier_fourier (f g : 𝓢(V, H)) :
    ∫ ξ, ⟪𝓕 f ξ, 𝓕 g ξ⟫ = ∫ x, ⟪f x, g x⟫ :=
  integral_sesq_fourier_fourier f g (innerSL ℂ)

set_option backward.isDefEq.respectTransparency false in
theorem integral_norm_sq_fourier (f : 𝓢(V, H)) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using
    integral_inner_fourier_fourier f f

theorem inner_fourier_toL2_eq (f g : 𝓢(V, H)) :
    ⟪(𝓕 f).toLp 2, (𝓕 g).toLp 2⟫ = ⟪f.toLp 2, g.toLp 2⟫ := by simp

@[deprecated (since := "2025-11-13")]
alias inner_fourierTransformCLM_toL2_eq := inner_fourier_toL2_eq

@[simp] theorem norm_fourier_toL2_eq (f : 𝓢(V, H)) :
    ‖(𝓕 f).toLp 2‖ = ‖f.toLp 2‖ := by
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_fourier_toL2_eq]

@[deprecated (since := "2025-11-13")]
alias norm_fourierTransformCLM_toL2_eq := norm_fourier_toL2_eq

end L2

end SchwartzMap
