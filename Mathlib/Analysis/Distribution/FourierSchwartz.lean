/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier transform on Schwartz functions

This file constructs the Fourier transform as a continuous linear map acting on Schwartz
functions, in `fourierTransformCLM`. It is also given as a continuous linear equiv, in
`fourierTransformCLE`.
-/

open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace

namespace SchwartzMap

variable
  (𝕜 : Type*) [RCLike 𝕜]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace 𝕜 W]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section definition

/-- The Fourier transform on a real inner product space, as a continuous linear map on the
Schwartz space. -/
noncomputable def fourierTransformCLM : 𝓢(V, E) →L[𝕜] 𝓢(V, E) := by
  refine mkCLM (𝓕 ·) ?_ ?_ ?_ ?_
  · intro f g x
    simp only [fourierIntegral_eq, add_apply, smul_add]
    rw [integral_add]
    · exact (fourierIntegral_convergent_iff _).2 f.integrable
    · exact (fourierIntegral_convergent_iff _).2 g.integrable
  · intro c f x
    simp only [fourierIntegral_eq, smul_apply, smul_comm _ c, integral_smul, RingHom.id_apply]
  · intro f
    exact Real.contDiff_fourierIntegral (fun n _ ↦ integrable_pow_mul volume f n)
  · rintro ⟨k, n⟩
    refine ⟨Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1),
       (2 * π) ^ n * (2 * ↑n + 2) ^ k * (Finset.range (n + 1) ×ˢ Finset.range (k + 1)).card
         * 2 ^ integrablePower (volume : Measure V) *
         (∫ (x : V), (1 + ‖x‖) ^ (- (integrablePower (volume : Measure V) : ℝ))) * 2,
       ⟨by positivity, fun f x ↦ ?_⟩⟩
    apply (pow_mul_norm_iteratedFDeriv_fourierIntegral_le (f.smooth ⊤)
      (fun k n _hk _hn ↦ integrable_pow_mul_iteratedFDeriv _ f k n) le_top le_top x).trans
    simp only [mul_assoc]
    gcongr
    calc
    ∑ p ∈ Finset.range (n + 1) ×ˢ Finset.range (k + 1),
        ∫ (v : V), ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 (⇑f) v‖
      ≤ ∑ p ∈ Finset.range (n + 1) ×ˢ Finset.range (k + 1),
        2 ^ integrablePower (volume : Measure V) *
        (∫ (x : V), (1 + ‖x‖) ^ (- (integrablePower (volume : Measure V) : ℝ))) * 2 *
        ((Finset.range (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1)).sup
          (schwartzSeminormFamily 𝕜 V E)) f := by
      gcongr with p hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      apply (f.integral_pow_mul_iteratedFDeriv_le 𝕜 _ _ _).trans
      simp only [mul_assoc]
      rw [two_mul]
      gcongr
      · apply Seminorm.le_def.1
        have : (0, p.2) ∈ (Finset.range (n + integrablePower (volume : Measure V) + 1)
            ×ˢ Finset.range (k + 1)) := by simp [hp.2]
        apply Finset.le_sup this (f := fun p ↦ SchwartzMap.seminorm 𝕜 p.1 p.2 (E := V) (F := E))
      · apply Seminorm.le_def.1
        have : (p.1 + integrablePower (volume : Measure V), p.2) ∈ (Finset.range
            (n + integrablePower (volume : Measure V) + 1) ×ˢ Finset.range (k + 1)) := by
          simp [hp.2]
          omega
        apply Finset.le_sup this (f := fun p ↦ SchwartzMap.seminorm 𝕜 p.1 p.2 (E := V) (F := E))
    _ = _ := by simp [mul_assoc]

/-- The Fourier transform on a real inner product space, as a continuous linear map on the
Schwartz space. -/
noncomputable def fourierTransform (f : 𝓢(V, E)) : 𝓢(V, E) := fourierTransformCLM ℂ f

@[simp]
theorem coe_fourierTransform (f : 𝓢(V, E)) : (f.fourierTransform : V → E) = 𝓕 f := rfl

theorem fourierTransform_apply (f : 𝓢(V, E)) (x : V) : f.fourierTransform x = 𝓕 f x := rfl

@[simp]
theorem fourierTransformCLM_apply (f : 𝓢(V, E)) :
    fourierTransformCLM 𝕜 f = f.fourierTransform := rfl

variable [CompleteSpace E]

@[simp]
theorem fourier_inversion (f : 𝓢(V, E)) (x : V) : 𝓕⁻ (𝓕 f) x = f x :=
  Integrable.fourier_inversion f.integrable (fourierTransformCLM ℂ f).integrable
    f.continuous.continuousAt

@[simp]
theorem fourier_inversion_inv (f : 𝓢(V, E)) (x : V) : 𝓕 (𝓕⁻ f) x = f x :=
  Integrable.fourier_inversion_inv f.integrable (fourierTransformCLM ℂ f).integrable
    f.continuous.continuousAt

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

variable [CompleteSpace F]

/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint.
Version where the multiplication is replaced by a general bilinear form `M`. -/
theorem integral_bilin_fourierIntegral_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕 g x) := by
  have := VectorFourier.integral_bilin_fourierIntegral_eq_flip M (μ := volume) (ν := volume)
    (L := (innerₗ V)) continuous_fourierChar continuous_inner f.integrable g.integrable
  rwa [flip_innerₗ] at this

theorem integral_sesq_fourierIntegral_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L⋆[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g x) := by
  have := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip M (μ := volume) (ν := volume)
    (L := (innerₗ V)) continuous_fourierChar continuous_inner f.integrable g.integrable
  rwa [flip_innerₗ] at this

/-- Plancherel's theorem for Schwartz functions.

Version where the multiplication is replaced by a general bilinear form `M`. -/
theorem integral_sesq_fourier_fourier (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L⋆[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (𝓕 g ξ) = ∫ x, M (f x) (g x) := by
  simpa only [fourierTransformCLM_apply, fourier_inversion]
    using integral_sesq_fourierIntegral_eq f (fourierTransformCLM ℂ g) M

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Plancherel's theorem for Schwartz functions. -/
theorem integral_inner_fourier_fourier (f g : 𝓢(V, H)) :
    ∫ ξ, ⟪𝓕 f ξ, 𝓕 g ξ⟫ = ∫ x, ⟪f x, g x⟫ :=
  integral_sesq_fourier_fourier f g (innerSL ℂ)

theorem integral_norm_sq_fourier (f : 𝓢(V, H)) :
    ∫ ξ, ‖𝓕 f ξ‖^2 = ∫ x, ‖f x‖^2 := by
  apply Complex.ofRealLI.injective
  simp only [← LinearIsometry.integral_comp_comm]
  convert integral_inner_fourier_fourier f f <;>
  simp [inner_self_eq_norm_sq_to_K]

theorem inner_fourierTransformCLM_toL2_eq (f : 𝓢(V, H)) :
    ⟪(fourierTransformCLM ℂ f).toLp 2, (fourierTransformCLM ℂ f).toLp 2⟫ =
    ⟪f.toLp 2, f.toLp 2⟫ := by
  simp only [inner_toL2_toL2_eq]
  exact integral_sesq_fourier_fourier f f (innerSL ℂ)

theorem norm_fourierTransformCLM_toL2_eq (f : 𝓢(V, H)) :
    ‖(fourierTransformCLM ℂ f).toLp 2‖ = ‖f.toLp 2‖ := by
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_fourierTransformCLM_toL2_eq]

/-- The Fourier transform on a real inner product space, as a continuous linear equiv on the
Schwartz space. -/
noncomputable def fourierTransformCLE : 𝓢(V, E) ≃L[𝕜] 𝓢(V, E) where
  __ := fourierTransformCLM 𝕜
  invFun := (compCLMOfContinuousLinearEquiv 𝕜 (LinearIsometryEquiv.neg ℝ (E := V)))
      ∘L (fourierTransformCLM 𝕜)
  left_inv := by
    intro f
    ext x
    change 𝓕 (𝓕 f) (-x) = f x
    rw [← fourierIntegralInv_eq_fourierIntegral_neg, Continuous.fourier_inversion f.continuous
      f.integrable (fourierTransformCLM 𝕜 f).integrable]
  right_inv := by
    intro f
    ext x
    change 𝓕 (fun x ↦ (𝓕 f) (-x)) x = f x
    simp_rw [← fourierIntegralInv_eq_fourierIntegral_neg, Continuous.fourier_inversion_inv
      f.continuous f.integrable (fourierTransformCLM 𝕜 f).integrable]
  continuous_invFun := ContinuousLinearMap.continuous _

@[simp]
theorem fourierTransformCLE_apply (f : 𝓢(V, E)) :
    fourierTransformCLE 𝕜 f = f.fourierTransform := rfl

/-- The Fourier transform on a real inner product space, as a continuous linear map on the
Schwartz space. -/
noncomputable def fourierTransformInv (f : 𝓢(V, E)) : 𝓢(V, E) := (fourierTransformCLE ℂ).symm f

@[simp]
theorem coe_fourierTransformInv (f : 𝓢(V, E)) : (f.fourierTransformInv : V → E) = 𝓕⁻ f := by
  ext x
  exact (fourierIntegralInv_eq_fourierIntegral_neg f x).symm

theorem fourierTransformInv_apply (f : 𝓢(V, E)) (x : V) : f.fourierTransformInv x = 𝓕⁻ f x :=
  (fourierIntegralInv_eq_fourierIntegral_neg f x).symm

@[simp]
theorem fourierTransformCLE_symm_apply (f : 𝓢(V, E)) :
    (fourierTransformCLE 𝕜).symm f = f.fourierTransformInv := by rfl

@[simp]
theorem fourier_inversion (f : 𝓢(V, E)) : f.fourierTransform.fourierTransformInv = f :=
  (fourierTransformCLE ℂ).left_inv f

@[simp]
theorem fourier_inversion_apply (f : 𝓢(V, E)) (x : V) : 𝓕⁻ (𝓕 f) x = f x := by
  rw [← coe_fourierTransform, ← fourierTransformInv_apply, fourier_inversion]

@[simp]
theorem fourier_inversion_inv (f : 𝓢(V, E)) : f.fourierTransformInv.fourierTransform = f :=
  (fourierTransformCLE ℂ).right_inv f

@[simp]
theorem fourier_inversion_inv_apply (f : 𝓢(V, E)) (x : V) : 𝓕 (𝓕⁻ f) x = f x := by
  rw [← coe_fourierTransformInv, ← fourierTransform_apply, fourier_inversion_inv]

end definition

section fubini

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace 𝕜 F] [SMulCommClass ℂ 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

variable [CompleteSpace E] [CompleteSpace F]

/-- The Fourier transform satisfies `∫ 𝓕 f * g = ∫ f * 𝓕 g`, i.e., it is self-adjoint.
Version where the multiplication is replaced by a general bilinear form `M`. -/
theorem integral_bilin_fourierIntegral_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕 g x) := by
  have := VectorFourier.integral_bilin_fourierIntegral_eq_flip M (μ := volume) (ν := volume)
    (L := (innerₗ V)) continuous_fourierChar continuous_inner f.integrable g.integrable
  rwa [flip_innerₗ] at this

theorem integral_sesq_fourierIntegral_eq (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L⋆[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (g ξ) = ∫ x, M (f x) (𝓕⁻ g x) := by
  have := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip M (μ := volume) (ν := volume)
    (L := (innerₗ V)) continuous_fourierChar continuous_inner f.integrable g.integrable
  rwa [flip_innerₗ] at this

/-- Plancherel's theorem for Schwartz functions. -/
theorem integral_sesq_fourier_fourier (f : 𝓢(V, E)) (g : 𝓢(V, F)) (M : E →L⋆[ℂ] F →L[ℂ] G) :
    ∫ ξ, M (𝓕 f ξ) (𝓕 g ξ) = ∫ x, M (f x) (g x) := by
  have := integral_sesq_fourierIntegral_eq f g.fourierTransform M
  simp only [fourierTransform_apply, coe_fourierTransform, fourier_inversion_apply] at this
  assumption

end fubini

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section toL2

theorem inner_fourierTransform_toL2_eq (f : 𝓢(V, H)) :
    inner ℂ (f.fourierTransform.toLp 2) (f.fourierTransform.toLp 2) =
    inner ℂ (f.toLp 2) (f.toLp 2) := by
  simp only [inner_toL2_toL2_eq]
  exact integral_sesq_fourier_fourier f f (innerSL ℂ)

theorem norm_fourierTransform_toL2_eq (f : 𝓢(V, H)) :
    ‖f.fourierTransform.toLp 2‖ = ‖f.toLp 2‖ := by
  simp_rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_fourierTransform_toL2_eq]

end toL2

end SchwartzMap
