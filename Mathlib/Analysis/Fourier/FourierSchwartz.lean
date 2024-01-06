/-
Copyright (c) 2024 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Frechet Derivative of the Fourier transform

In this file, we evaluate the Fréchet derivative of the Fourier transform

## Main result

* `hasFDerivAt_fourier` : The Fréchet derivative of the Fourier transform of `f` is the
    Fourier transform of `fun v ↦ ((-2 * π * I) • f v) ⊗ (innerSL ℝ v)`.

## Tags

Fourier tranform, Fréchet derivative

-/

open MeasureTheory Real Complex

variable (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

noncomputable section

abbrev integralFourier (f : E → F) :=
  (VectorFourier.fourierIntegral (E := F)) Real.fourierChar (volume : Measure E) (innerₛₗ ℝ) f

-- belongs in Mathlib.Analysis.InnerProductSpace.Calculus
-- TODO : Add after `HasFDerivAt.inner`
theorem hasFDerivAt_inner (𝕜 : Type*) {E : Type*} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (v : E) (x : E) : HasFDerivAt (inner (𝕜 := 𝕜) v)
    (innerSL 𝕜 v) x := (innerSL 𝕜 v).hasFDerivAt



attribute [continuity] continuous_ofAdd -- TO DO: tag where `continuous_ofAdd` is defined

/--
The Fréchet derivative of the Fourier transform of `f` is the Fourier transform of
`fun v ↦ ((-2 * π * I) • f v) ⊗ (innerSL ℝ v)`.
-/
theorem hasFDerivAt_fourier {f : E → F} (hf_int : Integrable f)
    (hvf_int : Integrable (fun v ↦ ‖v‖ * ‖f v‖)) (x : E) :
    HasFDerivAt (integralFourier E F f)
      (integralFourier E (E →L[ℝ] F) (fun v ↦
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(2 * π * I) • f v)) ∘L (innerSL ℝ) v)) x) x := by
  dsimp [integralFourier]
  let F' v w : E →L[ℝ] F := ((Real.fourierChar (Multiplicative.toAdd.symm ⟪w,v⟫_ℝ))⁻¹ : ℂ) •
    (ContinuousLinearMap.toSpanSingleton ℝ (-(2 * π * I) • f w)) ∘L ((innerSL ℝ) w)
  let bound v : ℝ := 2 * π * ‖f v‖ * ‖v‖
  convert hasFDerivAt_integral_of_dominated_of_fderiv_le
    (ε_pos := (by norm_num : (0:ℝ) < 1)) (bound := bound) (F' := F') _ _ _ _ _ _
  · simp only [VectorFourier.fourierIntegral, ofAdd_neg, map_inv, coe_inv_unitSphere, ofReal_mul,
      ofReal_ofNat, neg_smul, smul_neg, neg_mul, ← mul_smul]
    rfl
  · filter_upwards [] with w
    refine AEStronglyMeasurable.smul (Continuous.aestronglyMeasurable ?_)
      hf_int.aestronglyMeasurable
    apply Continuous.comp continuous_subtype_val
    continuity
  · refine (VectorFourier.fourier_integral_convergent_iff ?_ ?_ x).mp hf_int
    · exact continuous_fourierChar.comp  continuous_id'
    · exact continuous_inner
  · refine AEStronglyMeasurable.smul ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      apply Measurable.comp measurable_inv
      apply Continuous.measurable
      continuity
    · sorry
  · filter_upwards [] with w u hu
    simp only [Multiplicative.toAdd_symm_eq, neg_smul, norm_smul, norm_inv, norm_eq_of_mem_sphere,
      inv_one, one_mul, ge_iff_le]
    convert ContinuousLinearMap.op_norm_comp_le _ _
    · rw [ContinuousLinearMap.norm_toSpanSingleton]
      simp [norm_smul]
      left
      sorry
    · simp
    · infer_instance
    · infer_instance
  · sorry -- Integrable
  · -- checking the derivative formula
    filter_upwards [] with w
    intro u hu
    convert (((Complex.ofRealClm.hasFDerivAt.comp u (hasFDerivAt_inner ℝ w u)).const_mul
      (2 * π)).mul_const I).neg.cexp.smul_const (f w) using 1
    · ext1 y
      simp only [fourierChar, ofAdd_neg, map_inv, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
        coe_inv_unitSphere, expMapCircle_apply, ofReal_mul, ofReal_ofNat, smul_eq_mul,
        Function.comp_apply, ofRealClm_apply]
      rw [Complex.exp_neg]
      rfl
    · ext y
      simp only [fourierChar, Multiplicative.toAdd_symm_eq, MonoidHom.coe_mk, OneHom.coe_mk,
        toAdd_ofAdd, expMapCircle_apply, ofReal_mul, ofReal_ofNat,
        ContinuousLinearMap.toSpanSingleton, neg_smul, ContinuousLinearMap.coe_smul',
        ContinuousLinearMap.coe_comp', ContinuousLinearMap.coe_mk', innerSL_apply_coe,
        Pi.smul_apply, Function.comp_apply, LinearMap.toSpanSingleton_apply, smul_neg,
        ofRealClm_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.neg_apply,
        smul_eq_mul, neg_inj, ← mul_smul, ← smul_assoc, real_smul, Complex.exp_neg]
      rw [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp']
      simp only [innerSL_apply_coe, Pi.smul_apply, Function.comp_apply, ofRealClm_apply,
        smul_eq_mul]
      congr! 1
      ring
