/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Fourier inversion formula

In a finite-dimensional real inner product space, we show the Fourier inversion formula, i.e.,
`𝓕⁻ (𝓕 f) v = f v` if `f` and `𝓕 f` are integrable, and `f` is continuous at `v`. This is proved
in `MeasureTheory.Integrable.fourier_inversion`. See also `Continuous.fourier_inversion`
giving `𝓕⁻ (𝓕 f) = f` under an additional continuity assumption for `f`.

We use the following proof. A naïve computation gives
`𝓕⁻ (𝓕 f) v
= ∫_w exp (2 I π ⟪w, v⟫) 𝓕 f (w) dw
= ∫_w exp (2 I π ⟪w, v⟫) ∫_x, exp (-2 I π ⟪w, x⟫) f x dx) dw
= ∫_x (∫_ w, exp (2 I π ⟪w, v - x⟫ dw) f x dx `

However, the Fubini step does not make sense for lack of integrability, and the middle integral
`∫_ w, exp (2 I π ⟪w, v - x⟫ dw` (which one would like to be a Dirac at `v - x`) is not defined.
To gain integrability, one multiplies with a Gaussian function `exp (-c⁻¹ ‖w‖^2)`, with a large
(but finite) `c`. As this function converges pointwise to `1` when `c → ∞`, we get
`∫_w exp (2 I π ⟪w, v⟫) 𝓕 f (w) dw = lim_c ∫_w exp (-c⁻¹ ‖w‖^2 + 2 I π ⟪w, v⟫) 𝓕 f (w) dw`.
One can perform Fubini on the right hand side for fixed `c`, writing the integral as
`∫_x (∫_w exp (-c⁻¹‖w‖^2 + 2 I π ⟪w, v - x⟫ dw)) f x dx`.
The middle factor is the Fourier transform of a more and more flat function
(converging to the constant `1`), hence it becomes more and more concentrated, around the
point `v`. (Morally, it converges to the Dirac at `v`). Moreover, it has integral one.
Therefore, multiplying by `f` and integrating, one gets a term converging to `f v` as `c → ∞`.
Since it also converges to `𝓕⁻ (𝓕 f) v`, this proves the result.

To check the concentration property of the middle factor and the fact that it has integral one, we
rely on the explicit computation of the Fourier transform of Gaussians.
-/

open Filter MeasureTheory Complex FiniteDimensional Metric Real Bornology

open scoped Topology FourierTransform RealInnerProductSpace Complex

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E] {f : V → E}

namespace Real

lemma tendsto_integral_cexp_sq_smul (hf : Integrable f) :
    Tendsto (fun (c : ℝ) ↦ (∫ v : V, cexp (- c⁻¹ * ‖v‖^2) • f v))
      atTop (𝓝 (∫ v : V, f v)) := by
  apply tendsto_integral_filter_of_dominated_convergence _ _ _ hf.norm
  · filter_upwards with v
    nth_rewrite 2 [show f v = cexp (- (0 : ℝ) * ‖v‖^2) • f v by simp]
    apply (Tendsto.cexp _).smul_const
    exact tendsto_inv_atTop_zero.ofReal.neg.mul_const _
  · filter_upwards with c using
      AEStronglyMeasurable.smul (Continuous.aestronglyMeasurable (by continuity)) hf.1
  · filter_upwards [Ici_mem_atTop (0 : ℝ)] with c (hc : 0 ≤ c)
    filter_upwards with v
    simp only [ofReal_inv, neg_mul, norm_smul, Complex.norm_eq_abs]
    norm_cast
    conv_rhs => rw [← one_mul (‖f v‖)]
    gcongr
    simp only [abs_exp, exp_le_one_iff, Left.neg_nonpos_iff]
    positivity

variable [CompleteSpace E]

lemma tendsto_integral_gaussian_smul (hf : Integrable f) (h'f : Integrable (𝓕 f)) (v : V) :
    Tendsto (fun (c : ℝ) ↦
      ∫ w : V, ((π * c) ^ (finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * c * ‖v - w‖ ^ 2)) • f w)
    atTop (𝓝 (𝓕⁻ (𝓕 f) v)) := by
  have A : Tendsto (fun (c : ℝ) ↦ (∫ w : V, cexp (- c⁻¹ * ‖w‖^2 + 2 * π * I * ⟪v, w⟫)
       • (𝓕 f) w)) atTop (𝓝 (𝓕⁻ (𝓕 f) v)) := by
    have : Integrable (fun w ↦ 𝐞 ⟪w, v⟫ • (𝓕 f) w) := by
      have B : Continuous fun p : V × V => (- innerₗ V) p.1 p.2 := continuous_inner.neg
      simpa using
        (VectorFourier.fourierIntegral_convergent_iff Real.continuous_fourierChar B v).2 h'f
    convert tendsto_integral_cexp_sq_smul this using 4 with c w
    · rw [Submonoid.smul_def, Real.fourierChar_apply, smul_smul, ← Complex.exp_add, real_inner_comm]
      congr 3
      simp only [ofReal_mul, ofReal_ofNat]
      ring
    · simp [fourierIntegralInv_eq]
  have B : Tendsto (fun (c : ℝ) ↦ (∫ w : V,
        𝓕 (fun w ↦ cexp (- c⁻¹ * ‖w‖^2 + 2 * π * I * ⟪v, w⟫)) w • f w)) atTop
      (𝓝 (𝓕⁻ (𝓕 f) v)) := by
    apply A.congr'
    filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
    have J : Integrable (fun w ↦ cexp (- c⁻¹ * ‖w‖^2 + 2 * π * I * ⟪v, w⟫)) :=
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (by simpa) _ _
    simpa using (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V)
      Real.continuous_fourierChar continuous_inner J hf).symm
  apply B.congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  congr with w
  rw [fourierIntegral_gaussian_innerProductSpace' (by simpa)]
  congr
  · simp
  · simp; ring

lemma tendsto_integral_gaussian_smul' (hf : Integrable f) {v : V} (h'f : ContinuousAt f v) :
    Tendsto (fun (c : ℝ) ↦
      ∫ w : V, ((π * c : ℂ) ^ (finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * c * ‖v - w‖ ^ 2)) • f w)
    atTop (𝓝 (f v)) := by
  let φ : V → ℝ := fun w ↦ π ^ (finrank ℝ V / 2 : ℝ) * Real.exp (-π^2 * ‖w‖^2)
  have A : Tendsto (fun (c : ℝ) ↦ ∫ w : V, (c ^ finrank ℝ V * φ (c • (v - w))) • f w)
      atTop (𝓝 (f v)) := by
    apply tendsto_integral_comp_smul_smul_of_integrable'
    · exact fun x ↦ by positivity
    · rw [integral_mul_left, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity)]
      nth_rewrite 2 [← pow_one π]
      rw [← rpow_natCast, ← rpow_natCast, ← rpow_sub pi_pos, ← rpow_mul pi_nonneg,
        ← rpow_add pi_pos]
      ring_nf
      exact rpow_zero _
    · have A : Tendsto (fun (w : V) ↦ π^2 * ‖w‖^2) (cobounded V) atTop := by
        rw [tendsto_const_mul_atTop_of_pos (by positivity)]
        apply (tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop
      have B := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (finrank ℝ V / 2) 1
        zero_lt_one |>.comp A |>.const_mul (π ^ (-finrank ℝ V / 2 : ℝ))
      rw [mul_zero] at B
      convert B using 2 with x
      simp only [neg_mul, one_mul, Function.comp_apply, ← mul_assoc, ← rpow_natCast, φ]
      congr 1
      rw [mul_rpow (by positivity) (by positivity), ← rpow_mul pi_nonneg,
        ← rpow_mul (norm_nonneg _), ← mul_assoc, ← rpow_add pi_pos, mul_comm]
      congr <;> ring
    · exact hf
    · exact h'f
  have B : Tendsto
      (fun (c : ℝ) ↦ ∫ w : V, ((c^(1/2:ℝ)) ^ finrank ℝ V * φ ((c^(1/2:ℝ)) • (v - w))) • f w)
      atTop (𝓝 (f v)) :=
    A.comp (tendsto_rpow_atTop (by norm_num))
  apply B.congr'
  filter_upwards [Ioi_mem_atTop 0] with c (hc : 0 < c)
  congr with w
  rw [← coe_smul]
  congr
  rw [ofReal_mul, ofReal_mul, ofReal_exp, ← mul_assoc]
  congr
  · rw [mul_cpow_ofReal_nonneg pi_nonneg hc.le, ← rpow_natCast, ← rpow_mul hc.le, mul_comm,
      ofReal_cpow pi_nonneg, ofReal_cpow hc.le]
    simp [div_eq_inv_mul]
  · norm_cast
    simp only [one_div, norm_smul, Real.norm_eq_abs, mul_pow, _root_.sq_abs, neg_mul, neg_inj,
      ← rpow_natCast, ← rpow_mul hc.le, mul_assoc]
    norm_num

end Real

variable [CompleteSpace E]

/-- **Fourier inversion formula**: If a function `f` on a finite-dimensional real inner product
space is integrable, and its Fourier transform `𝓕 f` is also integrable, then `𝓕⁻ (𝓕 f) = f` at
continuity points of `f`. -/
theorem MeasureTheory.Integrable.fourier_inversion
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V}
    (hv : ContinuousAt f v) : 𝓕⁻ (𝓕 f) v = f v :=
  tendsto_nhds_unique (Real.tendsto_integral_gaussian_smul hf h'f v)
    (Real.tendsto_integral_gaussian_smul' hf hv)

/-- **Fourier inversion formula**: If a function `f` on a finite-dimensional real inner product
space is continuous, integrable, and its Fourier transform `𝓕 f` is also integrable,
then `𝓕⁻ (𝓕 f) = f`. -/
theorem Continuous.fourier_inversion (h : Continuous f)
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) :
    𝓕⁻ (𝓕 f) = f := by
  ext v
  exact hf.fourier_inversion h'f h.continuousAt

/-- **Fourier inversion formula**: If a function `f` on a finite-dimensional real inner product
space is integrable, and its Fourier transform `𝓕 f` is also integrable, then `𝓕 (𝓕⁻ f) = f` at
continuity points of `f`. -/
theorem MeasureTheory.Integrable.fourier_inversion_inv
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) {v : V}
    (hv : ContinuousAt f v) : 𝓕 (𝓕⁻ f) v = f v := by
  rw [fourierIntegralInv_comm]
  exact fourier_inversion hf h'f hv

/-- **Fourier inversion formula**: If a function `f` on a finite-dimensional real inner product
space is continuous, integrable, and its Fourier transform `𝓕 f` is also integrable,
then `𝓕 (𝓕⁻ f) = f`. -/
theorem Continuous.fourier_inversion_inv (h : Continuous f)
    (hf : Integrable f) (h'f : Integrable (𝓕 f)) :
    𝓕 (𝓕⁻ f) = f := by
  ext v
  exact hf.fourier_inversion_inv h'f h.continuousAt
