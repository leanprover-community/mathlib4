/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.Convex.Complex
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.MeasureTheory.Integral.Pi

#align_import analysis.special_functions.gaussian from "leanprover-community/mathlib"@"7982767093ae38cba236487f9c9dd9cd99f63c16"

/-!
# Gaussian integral

We prove various versions of the formula for the Gaussian integral:
* `integral_gaussian`: for real `b` we have `∫ x:ℝ, exp (-b * x^2) = sqrt (π / b)`.
* `integral_gaussian_complex`: for complex `b` with `0 < re b` we have
  `∫ x:ℝ, exp (-b * x^2) = (π / b) ^ (1 / 2)`.
* `integral_gaussian_Ioi` and `integral_gaussian_complex_Ioi`: variants for integrals over `Ioi 0`.
* `Complex.Gamma_one_half_eq`: the formula `Γ (1 / 2) = √π`.

We also prove, more generally, that the Fourier transform of the Gaussian is another Gaussian:

* `integral_cexp_quadratic`: general formula for `∫ (x : ℝ), exp (b * x ^ 2 + c * x + d)`
* `fourierIntegral_gaussian`: for all complex `b` and `t` with `0 < re b`, we have
  `∫ x:ℝ, exp (I * t * x) * exp (-b * x^2) = (π / b) ^ (1 / 2) * exp (-t ^ 2 / (4 * b))`.
* `fourierIntegral_gaussian_pi`: a variant with `b` and `t` scaled to give a more symmetric
  statement, and formulated in terms of the Fourier transform operator `𝓕`.

We also give versions of these formulas in finite-dimensional inner product spaces, see
`integral_cexp_neg_mul_sq_norm_add` and `fourierIntegral_gaussian_innerProductSpace`.

As an application, in `Real.tsum_exp_neg_mul_int_sq` and `Complex.tsum_exp_neg_mul_int_sq`, we use
Poisson summation to prove the identity
`∑' (n : ℤ), exp (-π * a * n ^ 2) = 1 / a ^ (1 / 2) * ∑' (n : ℤ), exp (-π / a * n ^ 2)`
for positive real `a`, or complex `a` with positive real part. (See also
`NumberTheory.ModularForms.JacobiTheta`.)
-/

noncomputable section

open Real Set MeasureTheory Filter Asymptotics

open scoped Real Topology FourierTransform RealInnerProductSpace BigOperators

open Complex hiding exp continuous_exp abs_of_nonneg sq_abs

theorem exp_neg_mul_rpow_isLittleO_exp_neg {p b : ℝ} (hb : 0 < b) (hp : 1 < p) :
    (fun x : ℝ => exp (- b * x ^ p)) =o[atTop] fun x : ℝ => exp (-x) := by
  rw [isLittleO_exp_comp_exp_comp]
  suffices Tendsto (fun x => x * (b * x ^ (p - 1) + -1)) atTop atTop by
    refine Tendsto.congr' ?_ this
    refine eventuallyEq_of_mem (Ioi_mem_atTop (0 : ℝ)) (fun x hx => ?_)
    rw [mem_Ioi] at hx
    rw [rpow_sub_one hx.ne']
    field_simp [hx.ne']
    ring
  apply Tendsto.atTop_mul_atTop tendsto_id
  refine tendsto_atTop_add_const_right atTop (-1 : ℝ) ?_
  exact Tendsto.const_mul_atTop hb (tendsto_rpow_atTop (by linarith))

theorem exp_neg_mul_sq_isLittleO_exp_neg {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => exp (-b * x ^ 2)) =o[atTop] fun x : ℝ => exp (-x) := by
  simp_rw [← rpow_two]
  exact exp_neg_mul_rpow_isLittleO_exp_neg hb one_lt_two
#align exp_neg_mul_sq_is_o_exp_neg exp_neg_mul_sq_isLittleO_exp_neg

theorem rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg (s : ℝ) {b p : ℝ} (hp : 1 < p) (hb : 0 < b) :
    (fun x : ℝ => x ^ s * exp (- b * x ^ p)) =o[atTop] fun x : ℝ => exp (-(1 / 2) * x) := by
  apply ((isBigO_refl (fun x : ℝ => x ^ s) atTop).mul_isLittleO
      (exp_neg_mul_rpow_isLittleO_exp_neg hb hp)).trans
  simpa only [mul_comm] using Real.Gamma_integrand_isLittleO s

theorem rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg {b : ℝ} (hb : 0 < b) (s : ℝ) :
    (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) =o[atTop] fun x : ℝ => exp (-(1 / 2) * x) := by
  simp_rw [← rpow_two]
  exact rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg s one_lt_two hb
#align rpow_mul_exp_neg_mul_sq_is_o_exp_neg rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg

theorem integrableOn_rpow_mul_exp_neg_rpow {p s : ℝ} (hs : -1 < s) (hp : 1 ≤ p) :
    IntegrableOn (fun x : ℝ => x ^ s * exp (- x ^ p)) (Ioi 0) := by
  obtain hp | hp := le_iff_lt_or_eq.mp hp
  · have h_exp : ∀ x, ContinuousAt (fun x => exp (- x)) x := fun x => continuousAt_neg.exp
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
    constructor
    · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
      refine IntegrableOn.mul_continuousOn ?_ ?_ isCompact_Icc
      · refine (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp ?_
        exact intervalIntegral.intervalIntegrable_rpow' hs
      · intro x _
        change ContinuousWithinAt ((fun x => exp (- x)) ∘ (fun x => x ^ p)) (Icc 0 1) x
        refine ContinuousAt.comp_continuousWithinAt (h_exp _) ?_
        exact continuousWithinAt_id.rpow_const (Or.inr (le_of_lt (lt_trans zero_lt_one hp)))
    · have h_rpow : ∀ (x r : ℝ), x ∈ Ici 1 → ContinuousWithinAt (fun x => x ^ r) (Ici 1) x := by
        intro _ _ hx
        refine continuousWithinAt_id.rpow_const (Or.inl ?_)
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
      refine integrable_of_isBigO_exp_neg (by norm_num : (0:ℝ) < 1 / 2)
        (ContinuousOn.mul (fun x hx => h_rpow x s hx) (fun x hx => ?_)) (IsLittleO.isBigO ?_)
      · change ContinuousWithinAt ((fun x => exp (- x)) ∘ (fun x => x ^ p)) (Ici 1) x
        exact ContinuousAt.comp_continuousWithinAt (h_exp _) (h_rpow x p hx)
      · convert rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg s hp (by norm_num : (0:ℝ) < 1) using 3
        rw [neg_mul, one_mul]
  · simp_rw [← hp, Real.rpow_one]
    convert Real.GammaIntegral_convergent (by linarith : 0 < s + 1) using 2
    rw [add_sub_cancel_right, mul_comm]

theorem integrableOn_rpow_mul_exp_neg_mul_rpow {p s b : ℝ} (hs : -1 < s) (hp : 1 ≤ p) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ s * exp (- b * x ^ p)) (Ioi 0) := by
  have hib : 0 < b ^ (-p⁻¹) := rpow_pos_of_pos hb _
  suffices IntegrableOn (fun x ↦ (b ^ (-p⁻¹)) ^ s * (x ^ s * exp (-x ^ p))) (Ioi 0) by
    rw [show 0 = b ^ (-p⁻¹) * 0 by rw [mul_zero], ← integrableOn_Ioi_comp_mul_left_iff _ _ hib]
    refine this.congr_fun (fun _ hx => ?_) measurableSet_Ioi
    rw [← mul_assoc, mul_rpow, mul_rpow, ← rpow_mul (z := p), neg_mul, neg_mul, inv_mul_cancel,
      rpow_neg_one, mul_inv_cancel_left₀]
    all_goals linarith [mem_Ioi.mp hx]
  refine Integrable.const_mul ?_ _
  rw [← IntegrableOn]
  exact integrableOn_rpow_mul_exp_neg_rpow hs hp

theorem integrableOn_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) (Ioi 0) := by
  simp_rw [← rpow_two]
  exact integrableOn_rpow_mul_exp_neg_mul_rpow hs one_le_two hb
#align integrable_on_rpow_mul_exp_neg_mul_sq integrableOn_rpow_mul_exp_neg_mul_sq

theorem integrable_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    Integrable fun x : ℝ => x ^ s * exp (-b * x ^ 2) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine' ⟨_, integrableOn_rpow_mul_exp_neg_mul_sq hb hs⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simp only [Function.comp, neg_sq, neg_preimage, preimage_neg_Iio, neg_neg, neg_zero]
  apply Integrable.mono' (integrableOn_rpow_mul_exp_neg_mul_sq hb hs)
  · apply Measurable.aestronglyMeasurable
    exact (measurable_id'.neg.pow measurable_const).mul
      ((measurable_id'.pow measurable_const).const_mul (-b)).exp
  · have : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_Ioi
    filter_upwards [ae_restrict_mem this] with x hx
    have h'x : 0 ≤ x := le_of_lt hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le]
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    simpa [abs_of_nonneg h'x] using abs_rpow_le_abs_rpow (-x) s
#align integrable_rpow_mul_exp_neg_mul_sq integrable_rpow_mul_exp_neg_mul_sq

theorem integrable_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) : Integrable fun x : ℝ => exp (-b * x ^ 2) :=
  by simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 0)
#align integrable_exp_neg_mul_sq integrable_exp_neg_mul_sq

theorem integrableOn_Ioi_exp_neg_mul_sq_iff {b : ℝ} :
    IntegrableOn (fun x : ℝ => exp (-b * x ^ 2)) (Ioi 0) ↔ 0 < b := by
  refine' ⟨fun h => _, fun h => (integrable_exp_neg_mul_sq h).integrableOn⟩
  by_contra! hb
  have : ∫⁻ _ : ℝ in Ioi 0, 1 ≤ ∫⁻ x : ℝ in Ioi 0, ‖exp (-b * x ^ 2)‖₊ := by
    apply lintegral_mono (fun x ↦ _)
    simp only [neg_mul, ENNReal.one_le_coe_iff, ← toNNReal_one, toNNReal_le_iff_le_coe,
      Real.norm_of_nonneg (exp_pos _).le, coe_nnnorm, one_le_exp_iff, Right.nonneg_neg_iff]
    exact fun x ↦ mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg x)
  simpa using this.trans_lt h.2
#align integrable_on_Ioi_exp_neg_mul_sq_iff integrableOn_Ioi_exp_neg_mul_sq_iff

theorem integrable_exp_neg_mul_sq_iff {b : ℝ} :
    (Integrable fun x : ℝ => exp (-b * x ^ 2)) ↔ 0 < b :=
  ⟨fun h => integrableOn_Ioi_exp_neg_mul_sq_iff.mp h.integrableOn, integrable_exp_neg_mul_sq⟩
#align integrable_exp_neg_mul_sq_iff integrable_exp_neg_mul_sq_iff

theorem integrable_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun x : ℝ => x * exp (-b * x ^ 2) := by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 1)
#align integrable_mul_exp_neg_mul_sq integrable_mul_exp_neg_mul_sq

theorem norm_cexp_neg_mul_sq (b : ℂ) (x : ℝ) :
    ‖Complex.exp (-b * (x : ℂ) ^ 2)‖ = exp (-b.re * x ^ 2) := by
  rw [Complex.norm_eq_abs, Complex.abs_exp, ← ofReal_pow, mul_comm (-b) _, re_ofReal_mul, neg_re,
    mul_comm]
#align norm_cexp_neg_mul_sq norm_cexp_neg_mul_sq

theorem integrable_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
    Integrable fun x : ℝ => cexp (-b * (x : ℂ) ^ 2) := by
  refine' ⟨(Complex.continuous_exp.comp
    (continuous_const.mul (continuous_ofReal.pow 2))).aestronglyMeasurable, _⟩
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_cexp_neg_mul_sq]
  exact (integrable_exp_neg_mul_sq hb).2
#align integrable_cexp_neg_mul_sq integrable_cexp_neg_mul_sq

theorem integrable_mul_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
    Integrable fun x : ℝ => ↑x * cexp (-b * (x : ℂ) ^ 2) := by
  refine' ⟨(continuous_ofReal.mul (Complex.continuous_exp.comp _)).aestronglyMeasurable, _⟩
  · exact continuous_const.mul (continuous_ofReal.pow 2)
  have := (integrable_mul_exp_neg_mul_sq hb).hasFiniteIntegral
  rw [← hasFiniteIntegral_norm_iff] at this ⊢
  convert this
  rw [norm_mul, norm_mul, norm_cexp_neg_mul_sq b, Complex.norm_eq_abs, abs_ofReal, Real.norm_eq_abs,
    norm_of_nonneg (exp_pos _).le]
#align integrable_mul_cexp_neg_mul_sq integrable_mul_cexp_neg_mul_sq

theorem integral_mul_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
    ∫ r : ℝ in Ioi 0, (r : ℂ) * cexp (-b * (r : ℂ) ^ 2) = (2 * b)⁻¹ := by
  have hb' : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
  have A : ∀ x : ℂ, HasDerivAt (fun x => -(2 * b)⁻¹ * cexp (-b * x ^ 2))
    (x * cexp (-b * x ^ 2)) x := by
    intro x
    convert ((hasDerivAt_pow 2 x).const_mul (-b)).cexp.const_mul (-(2 * b)⁻¹) using 1
    field_simp [hb']
    ring
  have B : Tendsto (fun y : ℝ ↦ -(2 * b)⁻¹ * cexp (-b * (y : ℂ) ^ 2))
    atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    refine' Tendsto.const_mul _ (tendsto_zero_iff_norm_tendsto_zero.mpr _)
    simp_rw [norm_cexp_neg_mul_sq b]
    exact tendsto_exp_atBot.comp (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.2 hb)
        (tendsto_pow_atTop two_ne_zero))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => (A ↑x).comp_ofReal)
    (integrable_mul_cexp_neg_mul_sq hb).integrableOn B using 1
  simp only [mul_zero, ofReal_zero, zero_pow, Ne.def, bit0_eq_zero, Nat.one_ne_zero,
    not_false_iff, Complex.exp_zero, mul_one, sub_neg_eq_add, zero_add]
#align integral_mul_cexp_neg_mul_sq integral_mul_cexp_neg_mul_sq

/-- The *square* of the Gaussian integral `∫ x:ℝ, exp (-b * x^2)` is equal to `π / b`. -/
theorem integral_gaussian_sq_complex {b : ℂ} (hb : 0 < b.re) :
    (∫ x : ℝ, cexp (-b * (x : ℂ) ^ 2)) ^ 2 = π / b := by
  /- We compute `(∫ exp (-b x^2))^2` as an integral over `ℝ^2`, and then make a polar change
  of coordinates. We are left with `∫ r * exp (-b r^2)`, which has been computed in
  `integral_mul_cexp_neg_mul_sq` using the fact that this function has an obvious primitive. -/
  calc
    (∫ x : ℝ, cexp (-b * (x : ℂ) ^ 2)) ^ 2 =
        ∫ p : ℝ × ℝ, cexp (-b * (p.1 : ℂ) ^ 2) * cexp (-b * (p.2 : ℂ) ^ 2) :=
      by rw [pow_two, ← integral_prod_mul]; rfl
    _ = ∫ p : ℝ × ℝ, cexp (-b * ((p.1 : ℂ)^ 2 + (p.2 : ℂ) ^ 2)) := by
      congr
      ext1 p
      rw [← Complex.exp_add, mul_add]
    _ = ∫ p in polarCoord.target, p.1 •
        cexp (-b * ((p.1 * Complex.cos p.2) ^ 2 + (p.1 * Complex.sin p.2) ^ 2)) := by
      rw [← integral_comp_polarCoord_symm]
      simp only [polarCoord_symm_apply, ofReal_mul, ofReal_cos, ofReal_sin]
    _ = (∫ r in Ioi (0 : ℝ), r * cexp (-b * (r : ℂ) ^ 2)) * ∫ θ in Ioo (-π) π, 1 := by
      rw [← set_integral_prod_mul]
      congr with p : 1
      rw [mul_one]
      congr
      conv_rhs => rw [← one_mul ((p.1 : ℂ) ^ 2), ← sin_sq_add_cos_sq (p.2 : ℂ)]
      ring
    _ = ↑π / b := by
      have : 0 ≤ π + π := by linarith [Real.pi_pos]
      simp only [integral_const, Measure.restrict_apply', measurableSet_Ioo, univ_inter, volume_Ioo,
        sub_neg_eq_add, ENNReal.toReal_ofReal, this]
      rw [← two_mul, real_smul, mul_one, ofReal_mul, ofReal_ofNat, integral_mul_cexp_neg_mul_sq hb]
      field_simp [(by contrapose! hb; rw [hb, zero_re] : b ≠ 0)]
      ring
#align integral_gaussian_sq_complex integral_gaussian_sq_complex

theorem integral_gaussian (b : ℝ) : ∫ x : ℝ, exp (-b * x ^ 2) = sqrt (π / b) := by
  -- First we deal with the crazy case where `b ≤ 0`: then both sides vanish.
  rcases le_or_lt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · simpa only [not_lt, integrable_exp_neg_mul_sq_iff] using hb
  -- Assume now `b > 0`. Then both sides are non-negative and their squares agree.
  refine' (sq_eq_sq (by positivity) (by positivity)).1 _
  rw [← ofReal_inj, ofReal_pow, ← coe_algebraMap, RCLike.algebraMap_eq_ofReal, ← integral_ofReal,
    sq_sqrt (div_pos pi_pos hb).le, ← RCLike.algebraMap_eq_ofReal, coe_algebraMap, ofReal_div]
  convert integral_gaussian_sq_complex (by rwa [ofReal_re] : 0 < (b : ℂ).re) with _ x
  rw [ofReal_exp, ofReal_mul, ofReal_pow, ofReal_neg]
#align integral_gaussian integral_gaussian

theorem continuousAt_gaussian_integral (b : ℂ) (hb : 0 < re b) :
    ContinuousAt (fun c : ℂ => ∫ x : ℝ, cexp (-c * (x : ℂ) ^ 2)) b := by
  let f : ℂ → ℝ → ℂ := fun (c : ℂ) (x : ℝ) => cexp (-c * (x : ℂ) ^ 2)
  obtain ⟨d, hd, hd'⟩ := exists_between hb
  have f_meas : ∀ c : ℂ, AEStronglyMeasurable (f c) volume := fun c => by
    apply Continuous.aestronglyMeasurable
    exact Complex.continuous_exp.comp (continuous_const.mul (continuous_ofReal.pow 2))
  have f_cts : ∀ x : ℝ, ContinuousAt (fun c => f c x) b := fun x =>
    (Complex.continuous_exp.comp (continuous_id'.neg.mul continuous_const)).continuousAt
  have f_le_bd : ∀ᶠ c : ℂ in 𝓝 b, ∀ᵐ x : ℝ, ‖f c x‖ ≤ exp (-d * x ^ 2) := by
    refine' eventually_of_mem ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hd') _
    intro c hc; filter_upwards with x
    rw [norm_cexp_neg_mul_sq]
    gcongr
    exact le_of_lt hc
  exact
    continuousAt_of_dominated (eventually_of_forall f_meas) f_le_bd (integrable_exp_neg_mul_sq hd)
      (ae_of_all _ f_cts)
#align continuous_at_gaussian_integral continuousAt_gaussian_integral

theorem integral_gaussian_complex {b : ℂ} (hb : 0 < re b) :
    ∫ x : ℝ, cexp (-b * (x : ℂ) ^ 2) = (π / b) ^ (1 / 2 : ℂ) := by
  have nv : ∀ {b : ℂ}, 0 < re b → b ≠ 0 := by intro b hb; contrapose! hb; rw [hb]; simp
  apply
    (convex_halfspace_re_gt 0).isPreconnected.eq_of_sq_eq ?_ ?_ (fun c hc => ?_) (fun {c} hc => ?_)
      (by simp : 0 < re (1 : ℂ)) ?_ hb
  · -- integral is continuous
    exact ContinuousAt.continuousOn continuousAt_gaussian_integral
  · -- `(π / b) ^ (1 / 2 : ℂ)` is continuous
    refine'
      ContinuousAt.continuousOn fun b hb =>
        (continuousAt_cpow_const (Or.inl _)).comp (continuousAt_const.div continuousAt_id (nv hb))
    rw [div_re, ofReal_im, ofReal_re, zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos pi_pos hb) (normSq_pos.mpr (nv hb))
  · -- equality at 1
    have : ∀ x : ℝ, cexp (-(1 : ℂ) * (x : ℂ) ^ 2) = exp (-(1 : ℝ) * x ^ 2) := by
      intro x
      simp only [ofReal_exp, neg_mul, one_mul, ofReal_neg, ofReal_pow]
    simp_rw [this, ← coe_algebraMap, RCLike.algebraMap_eq_ofReal, integral_ofReal,
      ← RCLike.algebraMap_eq_ofReal, coe_algebraMap]
    conv_rhs =>
      congr
      · rw [← ofReal_one, ← ofReal_div]
      · rw [← ofReal_one, ← ofReal_ofNat, ← ofReal_div]
    rw [← ofReal_cpow, ofReal_inj]
    convert integral_gaussian (1 : ℝ) using 1
    · rw [sqrt_eq_rpow]
    · rw [div_one]; exact pi_pos.le
  · -- squares of both sides agree
    dsimp only [Pi.pow_apply]
    rw [integral_gaussian_sq_complex hc, sq]
    conv_lhs => rw [← cpow_one (↑π / c)]
    rw [← cpow_add _ _ (div_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) (nv hc))]
    norm_num
  · -- RHS doesn't vanish
    rw [Ne.def, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (div_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) (nv hc))
#align integral_gaussian_complex integral_gaussian_complex

-- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for complex `b`.
theorem integral_gaussian_complex_Ioi {b : ℂ} (hb : 0 < re b) :
    ∫ x : ℝ in Ioi 0, cexp (-b * (x : ℂ) ^ 2) = (π / b) ^ (1 / 2 : ℂ) / 2 := by
  have full_integral := integral_gaussian_complex hb
  have : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_Ioi
  rw [← integral_add_compl this (integrable_cexp_neg_mul_sq hb), compl_Ioi] at full_integral
  suffices ∫ x : ℝ in Iic 0, cexp (-b * (x : ℂ) ^ 2) = ∫ x : ℝ in Ioi 0, cexp (-b * (x : ℂ) ^ 2) by
    rw [this, ← mul_two] at full_integral
    rwa [eq_div_iff]; exact two_ne_zero
  have : ∀ c : ℝ, ∫ x in (0 : ℝ)..c, cexp (-b * (x : ℂ) ^ 2) =
      ∫ x in -c..0, cexp (-b * (x : ℂ) ^ 2) := by
    intro c
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := c)
      (fun x => cexp (-b * (x : ℂ) ^ 2)) 0
    simpa [zero_sub, neg_sq, neg_zero] using this
  have t1 :=
    intervalIntegral_tendsto_integral_Ioi 0 (integrable_cexp_neg_mul_sq hb).integrableOn tendsto_id
  have t2 :
    Tendsto (fun c : ℝ => ∫ x : ℝ in (0 : ℝ)..c, cexp (-b * (x : ℂ) ^ 2)) atTop
      (𝓝 (∫ x : ℝ in Iic 0, cexp (-b * (x : ℂ) ^ 2))) := by
    simp_rw [this]
    refine' intervalIntegral_tendsto_integral_Iic _ _ tendsto_neg_atTop_atBot
    apply (integrable_cexp_neg_mul_sq hb).integrableOn
  exact tendsto_nhds_unique t2 t1
#align integral_gaussian_complex_Ioi integral_gaussian_complex_Ioi

-- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for real `b`.
theorem integral_gaussian_Ioi (b : ℝ) :
    ∫ x in Ioi (0 : ℝ), exp (-b * x ^ 2) = sqrt (π / b) / 2 := by
  rcases le_or_lt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos, zero_div]
    exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    rwa [← IntegrableOn, integrableOn_Ioi_exp_neg_mul_sq_iff, not_lt]
  rw [← RCLike.ofReal_inj (K := ℂ), ← integral_ofReal, ← RCLike.algebraMap_eq_ofReal,
    coe_algebraMap]
  convert integral_gaussian_complex_Ioi (by rwa [ofReal_re] : 0 < (b : ℂ).re)
  · simp
  · rw [sqrt_eq_rpow, ← ofReal_div, ofReal_div, ofReal_cpow]
    norm_num
    exact (div_pos pi_pos hb).le
#align integral_gaussian_Ioi integral_gaussian_Ioi

/-- The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian integral. -/
theorem Real.Gamma_one_half_eq : Real.Gamma (1 / 2) = sqrt π := by
  rw [Gamma_eq_integral one_half_pos, ← integral_comp_rpow_Ioi_of_pos zero_lt_two]
  convert congr_arg (fun x : ℝ => 2 * x) (integral_gaussian_Ioi 1) using 1
  · rw [← integral_mul_left]
    refine' set_integral_congr measurableSet_Ioi fun x hx => _
    dsimp only
    have : (x ^ (2 : ℝ)) ^ (1 / (2 : ℝ) - 1) = x⁻¹ := by
      rw [← rpow_mul (le_of_lt hx)]
      norm_num
      rw [rpow_neg (le_of_lt hx), rpow_one]
    rw [smul_eq_mul, this]
    field_simp [(ne_of_lt (show 0 < x from hx)).symm]
    norm_num; ring
  · rw [div_one, ← mul_div_assoc, mul_comm, mul_div_cancel_right₀ _ (two_ne_zero' ℝ)]
set_option linter.uppercaseLean3 false in
#align real.Gamma_one_half_eq Real.Gamma_one_half_eq

/-- The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian integral. -/
theorem Complex.Gamma_one_half_eq : Complex.Gamma (1 / 2) = (π : ℂ) ^ (1 / 2 : ℂ) := by
  convert congr_arg ((↑) : ℝ → ℂ) Real.Gamma_one_half_eq
  · simpa only [one_div, ofReal_inv, ofReal_ofNat] using Gamma_ofReal (1 / 2)
  · rw [sqrt_eq_rpow, ofReal_cpow pi_pos.le, ofReal_div, ofReal_ofNat, ofReal_one]
set_option linter.uppercaseLean3 false in
#align complex.Gamma_one_half_eq Complex.Gamma_one_half_eq

namespace GaussianFourier

/-!
## Fourier integral of Gaussian functions
-/

open intervalIntegral

open scoped Real

variable {b : ℂ}

/-- The integral of the Gaussian function over the vertical edges of a rectangle
with vertices at `(±T, 0)` and `(±T, c)`.  -/
def verticalIntegral (b : ℂ) (c T : ℝ) : ℂ :=
  ∫ y : ℝ in (0 : ℝ)..c, I * (cexp (-b * (T + y * I) ^ 2) - cexp (-b * (T - y * I) ^ 2))
#align gaussian_fourier.vertical_integral GaussianFourier.verticalIntegral

/-- Explicit formula for the norm of the Gaussian function along the vertical
edges. -/
theorem norm_cexp_neg_mul_sq_add_mul_I (b : ℂ) (c T : ℝ) :
    ‖cexp (-b * (T + c * I) ^ 2)‖ = exp (-(b.re * T ^ 2 - 2 * b.im * c * T - b.re * c ^ 2)) := by
  rw [Complex.norm_eq_abs, Complex.abs_exp, neg_mul, neg_re, ← re_add_im b]
  simp only [sq, re_add_im, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im]
  ring_nf
set_option linter.uppercaseLean3 false in
#align gaussian_fourier.norm_cexp_neg_mul_sq_add_mul_I GaussianFourier.norm_cexp_neg_mul_sq_add_mul_I

theorem norm_cexp_neg_mul_sq_add_mul_I' (hb : b.re ≠ 0) (c T : ℝ) :
    ‖cexp (-b * (T + c * I) ^ 2)‖ =
      exp (-(b.re * (T - b.im * c / b.re) ^ 2 - c ^ 2 * (b.im ^ 2 / b.re + b.re))) := by
  have :
    b.re * T ^ 2 - 2 * b.im * c * T - b.re * c ^ 2 =
      b.re * (T - b.im * c / b.re) ^ 2 - c ^ 2 * (b.im ^ 2 / b.re + b.re) :=
    by field_simp; ring
  rw [norm_cexp_neg_mul_sq_add_mul_I, this]
set_option linter.uppercaseLean3 false in
#align gaussian_fourier.norm_cexp_neg_mul_sq_add_mul_I' GaussianFourier.norm_cexp_neg_mul_sq_add_mul_I'

theorem verticalIntegral_norm_le (hb : 0 < b.re) (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ‖verticalIntegral b c T‖ ≤
      (2 : ℝ) * |c| * exp (-(b.re * T ^ 2 - (2 : ℝ) * |b.im| * |c| * T - b.re * c ^ 2)) := by
  -- first get uniform bound for integrand
  have vert_norm_bound :
    ∀ {T : ℝ},
      0 ≤ T →
        ∀ {c y : ℝ},
          |y| ≤ |c| →
            ‖cexp (-b * (T + y * I) ^ 2)‖ ≤
              exp (-(b.re * T ^ 2 - (2 : ℝ) * |b.im| * |c| * T - b.re * c ^ 2)) := by
    intro T hT c y hy
    rw [norm_cexp_neg_mul_sq_add_mul_I b]
    gcongr exp (- (_ - ?_ * _ - _ * ?_))
    · (conv_lhs => rw [mul_assoc]); (conv_rhs => rw [mul_assoc])
      gcongr _ * ?_
      refine' (le_abs_self _).trans _
      rw [abs_mul]
      gcongr
    · rwa [sq_le_sq]
  -- now main proof
  refine' (intervalIntegral.norm_integral_le_of_norm_le_const _).trans _
  pick_goal 3
  · rw [sub_zero]
    conv_lhs => simp only [mul_comm _ |c|]
    conv_rhs =>
      conv =>
        congr
        rw [mul_comm]
      rw [mul_assoc]
  · intro y hy
    have absy : |y| ≤ |c| := by
      rcases le_or_lt 0 c with (h | h)
      · rw [uIoc_of_le h] at hy
        rw [abs_of_nonneg h, abs_of_pos hy.1]
        exact hy.2
      · rw [uIoc_of_lt h] at hy
        rw [abs_of_neg h, abs_of_nonpos hy.2, neg_le_neg_iff]
        exact hy.1.le
    rw [norm_mul, Complex.norm_eq_abs, abs_I, one_mul, two_mul]
    refine' (norm_sub_le _ _).trans (add_le_add (vert_norm_bound hT absy) _)
    rw [← abs_neg y] at absy
    simpa only [neg_mul, ofReal_neg] using vert_norm_bound hT absy
#align gaussian_fourier.vertical_integral_norm_le GaussianFourier.verticalIntegral_norm_le

theorem tendsto_verticalIntegral (hb : 0 < b.re) (c : ℝ) :
    Tendsto (verticalIntegral b c) atTop (𝓝 0) := by
  -- complete proof using squeeze theorem:
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine'
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds _
      (eventually_of_forall fun _ => norm_nonneg _)
      ((eventually_ge_atTop (0 : ℝ)).mp
        (eventually_of_forall fun T hT => verticalIntegral_norm_le hb c hT))
  rw [(by ring : 0 = 2 * |c| * 0)]
  refine' (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp _)).const_mul _
  apply tendsto_atTop_add_const_right
  simp_rw [sq, ← mul_assoc, ← sub_mul]
  refine' Tendsto.atTop_mul_atTop (tendsto_atTop_add_const_right _ _ _) tendsto_id
  exact (tendsto_const_mul_atTop_of_pos hb).mpr tendsto_id
#align gaussian_fourier.tendsto_vertical_integral GaussianFourier.tendsto_verticalIntegral

theorem integrable_cexp_neg_mul_sq_add_real_mul_I (hb : 0 < b.re) (c : ℝ) :
    Integrable fun x : ℝ => cexp (-b * (x + c * I) ^ 2) := by
  refine'
    ⟨(Complex.continuous_exp.comp
          (continuous_const.mul
            ((continuous_ofReal.add continuous_const).pow 2))).aestronglyMeasurable,
      _⟩
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_cexp_neg_mul_sq_add_mul_I' hb.ne', neg_sub _ (c ^ 2 * _),
    sub_eq_add_neg _ (b.re * _), Real.exp_add]
  suffices Integrable fun x : ℝ => exp (-(b.re * x ^ 2)) by
    exact (Integrable.comp_sub_right this (b.im * c / b.re)).hasFiniteIntegral.const_mul _
  simp_rw [← neg_mul]
  apply integrable_exp_neg_mul_sq hb
set_option linter.uppercaseLean3 false in
#align gaussian_fourier.integrable_cexp_neg_mul_sq_add_real_mul_I GaussianFourier.integrable_cexp_neg_mul_sq_add_real_mul_I

theorem integral_cexp_neg_mul_sq_add_real_mul_I (hb : 0 < b.re) (c : ℝ) :
    ∫ x : ℝ, cexp (-b * (x + c * I) ^ 2) = (π / b) ^ (1 / 2 : ℂ) := by
  refine'
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral (integrable_cexp_neg_mul_sq_add_real_mul_I hb c)
        tendsto_neg_atTop_atBot tendsto_id)
      _
  set I₁ := fun T => ∫ x : ℝ in -T..T, cexp (-b * (x + c * I) ^ 2) with HI₁
  let I₂ := fun T : ℝ => ∫ x : ℝ in -T..T, cexp (-b * (x : ℂ) ^ 2)
  let I₄ := fun T : ℝ => ∫ y : ℝ in (0 : ℝ)..c, cexp (-b * (T + y * I) ^ 2)
  let I₅ := fun T : ℝ => ∫ y : ℝ in (0 : ℝ)..c, cexp (-b * (-T + y * I) ^ 2)
  have C : ∀ T : ℝ, I₂ T - I₁ T + I * I₄ T - I * I₅ T = 0 := by
    intro T
    have :=
      integral_boundary_rect_eq_zero_of_differentiableOn (fun z => cexp (-b * z ^ 2)) (-T)
        (T + c * I)
        (by
          refine' Differentiable.differentiableOn (Differentiable.const_mul _ _).cexp
          exact differentiable_pow 2)
    simpa only [neg_im, ofReal_im, neg_zero, ofReal_zero, zero_mul, add_zero, neg_re,
      ofReal_re, add_re, mul_re, I_re, mul_zero, I_im, tsub_zero, add_im, mul_im,
      mul_one, zero_add, Algebra.id.smul_eq_mul, ofReal_neg] using this
  simp_rw [id.def, ← HI₁]
  have : I₁ = fun T : ℝ => I₂ T + verticalIntegral b c T := by
    ext1 T
    specialize C T
    rw [sub_eq_zero] at C
    unfold verticalIntegral
    rw [integral_const_mul, intervalIntegral.integral_sub]
    · simp_rw [(fun a b => by rw [sq]; ring_nf : ∀ a b : ℂ, (a - b * I) ^ 2 = (-a + b * I) ^ 2)]
      change I₁ T = I₂ T + I * (I₄ T - I₅ T)
      rw [mul_sub, ← C]
      abel
    all_goals apply Continuous.intervalIntegrable; continuity
  rw [this, ← add_zero ((π / b : ℂ) ^ (1 / 2 : ℂ)), ← integral_gaussian_complex hb]
  refine' Tendsto.add _ (tendsto_verticalIntegral hb c)
  exact
    intervalIntegral_tendsto_integral (integrable_cexp_neg_mul_sq hb) tendsto_neg_atTop_atBot
      tendsto_id
set_option linter.uppercaseLean3 false in
#align gaussian_fourier.integral_cexp_neg_mul_sq_add_real_mul_I GaussianFourier.integral_cexp_neg_mul_sq_add_real_mul_I

theorem _root_.integral_cexp_quadratic (hb : b.re < 0) (c d : ℂ) :
    ∫ x : ℝ, cexp (b * x ^ 2 + c * x + d) = (π / -b) ^ (1 / 2 : ℂ) * cexp (d - c^2 / (4 * b)) := by
  have hb' : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
  have h (x : ℝ) : cexp (b * x ^ 2 + c * x + d) =
      cexp (- -b * (x + c / (2 * b)) ^ 2) * cexp (d - c ^ 2 / (4 * b)) := by
    simp_rw [← Complex.exp_add]
    congr 1
    field_simp
    ring_nf
  simp_rw [h, integral_mul_right]
  rw [← re_add_im (c / (2 * b))]
  simp_rw [← add_assoc, ← ofReal_add]
  rw [integral_add_right_eq_self fun a : ℝ ↦ cexp (- -b * (↑a + ↑(c / (2 * b)).im * I) ^ 2),
    integral_cexp_neg_mul_sq_add_real_mul_I ((neg_re b).symm ▸ (neg_pos.mpr hb))]

lemma _root_.integrable_cexp_quadratic' (hb : b.re < 0) (c d : ℂ) :
    Integrable (fun (x : ℝ) ↦ cexp (b * x ^ 2 + c * x + d)) := by
  have hb' : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
  by_contra H
  simpa [hb', pi_ne_zero, Complex.exp_ne_zero, integral_undef H]
    using integral_cexp_quadratic hb c d

lemma _root_.integrable_cexp_quadratic (hb : 0 < b.re) (c d : ℂ) :
    Integrable (fun (x : ℝ) ↦ cexp (-b * x ^ 2 + c * x + d)) := by
  have : (-b).re < 0 := by simpa using hb
  exact integrable_cexp_quadratic' this c d

theorem _root_.fourierIntegral_gaussian (hb : 0 < b.re) (t : ℂ) :
    ∫ x : ℝ, cexp (I * t * x) * cexp (-b * x ^ 2) =
    (π / b) ^ (1 / 2 : ℂ) * cexp (-t ^ 2 / (4 * b)) := by
  conv => enter [1, 2, x]; rw [← Complex.exp_add, add_comm, ← add_zero (-b * x ^ 2 + I * t * x)]
  rw [integral_cexp_quadratic (show (-b).re < 0 by rwa [neg_re, neg_lt_zero]), neg_neg, zero_sub,
    mul_neg, div_neg, neg_neg, mul_pow, I_sq, neg_one_mul, mul_comm]
#align fourier_transform_gaussian fourierIntegral_gaussian

@[deprecated] alias _root_.fourier_transform_gaussian :=
  fourierIntegral_gaussian -- deprecated on 2024-02-21

theorem _root_.fourierIntegral_gaussian_pi' (hb : 0 < b.re) (c : ℂ) :
    (𝓕 fun x : ℝ => cexp (-π * b * x ^ 2 + 2 * π * c * x)) = fun t : ℝ =>
    1 / b ^ (1 / 2 : ℂ) * cexp (-π / b * (t + I * c) ^ 2) := by
  haveI : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
  have h : (-↑π * b).re < 0 := by
    simpa only [neg_mul, neg_re, re_ofReal_mul, neg_lt_zero] using mul_pos pi_pos hb
  ext1 t
  simp_rw [fourierIntegral_real_eq_integral_exp_smul, smul_eq_mul, ← Complex.exp_add, ← add_assoc]
  have (x : ℝ) : ↑(-2 * π * x * t) * I + -π * b * x ^ 2 + 2 * π * c * x =
    -π * b * x ^ 2 + (-2 * π * I * t + 2 * π * c) * x + 0 := by push_cast; ring
  simp_rw [this, integral_cexp_quadratic h, neg_mul, neg_neg]
  congr 2
  · rw [← div_div, div_self <| ofReal_ne_zero.mpr pi_ne_zero, one_div, inv_cpow, ← one_div]
    rw [Ne.def, arg_eq_pi_iff, not_and_or, not_lt]
    exact Or.inl hb.le
  · field_simp [ofReal_ne_zero.mpr pi_ne_zero]
    ring_nf
    simp only [I_sq]
    ring

@[deprecated] alias _root_.fourier_transform_gaussian_pi' :=
  _root_.fourierIntegral_gaussian_pi' -- deprecated on 2024-02-21

theorem _root_.fourierIntegral_gaussian_pi (hb : 0 < b.re) :
    (𝓕 fun (x : ℝ) ↦ cexp (-π * b * x ^ 2)) =
    fun t : ℝ ↦ 1 / b ^ (1 / 2 : ℂ) * cexp (-π / b * t ^ 2) := by
  simpa only [mul_zero, zero_mul, add_zero] using fourierIntegral_gaussian_pi' hb 0
#align fourier_transform_gaussian_pi fourierIntegral_gaussian_pi

@[deprecated] alias root_.fourier_transform_gaussian_pi :=
  _root_.fourierIntegral_gaussian_pi   -- deprecated on 2024-02-21

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

open scoped BigOperators

theorem integrable_cexp_neg_sum_mul_add {ι : Type*} [Fintype ι] {b : ι → ℂ}
    (hb : ∀ i, 0 < (b i).re) (c : ι → ℂ) :
    Integrable (fun (v : ι → ℝ) ↦ cexp (- ∑ i, b i * (v i : ℂ) ^ 2 + ∑ i, c i * v i)) := by
  simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Complex.exp_sum, ← neg_mul]
  apply Integrable.fintype_prod (f := fun i (v : ℝ) ↦ cexp (-b i * v^2 + c i * v)) (fun i ↦ ?_)
  convert integrable_cexp_quadratic (hb i) (c i) 0 using 3 with x
  simp only [add_zero]

theorem integrable_cexp_neg_mul_sum_add {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c : ι → ℂ) :
    Integrable (fun (v : ι → ℝ) ↦ cexp (- b * ∑ i, (v i : ℂ) ^ 2 + ∑ i, c i * v i)) := by
  simp_rw [neg_mul, Finset.mul_sum]
  exact integrable_cexp_neg_sum_mul_add (fun _ ↦ hb) c

theorem integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c : ℂ) (w : EuclideanSpace ℝ ι) :
    Integrable (fun (v : EuclideanSpace ℝ ι) ↦ cexp (- b * ‖v‖^2 + c * ⟪w, v⟫)) := by
  have := EuclideanSpace.volume_preserving_measurableEquiv ι
  rw [← MeasurePreserving.integrable_comp_emb this.symm (MeasurableEquiv.measurableEmbedding _)]
  simp only [neg_mul, Function.comp_def]
  convert integrable_cexp_neg_mul_sum_add hb (fun i ↦ c * w i) using 3 with v
  simp only [EuclideanSpace.measurableEquiv, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
    EuclideanSpace.norm_eq, WithLp.equiv_symm_pi_apply, Real.norm_eq_abs, sq_abs, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, ofReal_sum, ofReal_mul, Finset.mul_sum, neg_mul,
    Finset.sum_neg_distrib, mul_assoc, add_left_inj, neg_inj]
  norm_cast
  rw [sq_sqrt]
  · simp [Finset.mul_sum]
  · exact Finset.sum_nonneg (fun i _hi ↦ by positivity)

/-- In a real inner product space, the complex exponential of minus the square of the norm plus
a scalar product is integrable. Useful when discussing the Fourier transform of a Gaussian. -/
theorem integrable_cexp_neg_mul_sq_norm_add (hb : 0 < b.re) (c : ℂ) (w : V) :
    Integrable (fun (v : V) ↦ cexp (-b * ‖v‖^2 + c * ⟪w, v⟫)) := by
  let e := (stdOrthonormalBasis ℝ V).repr.symm
  rw [← e.measurePreserving.integrable_comp_emb e.toHomeomorph.measurableEmbedding]
  convert integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    hb c (e.symm w) with v
  simp only [neg_mul, Function.comp_apply, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.symm_symm, conj_trivial, ofReal_sum,
    ofReal_mul, LinearIsometryEquiv.inner_map_eq_flip]

theorem integral_cexp_neg_sum_mul_add {ι : Type*} [Fintype ι] {b : ι → ℂ}
    (hb : ∀ i, 0 < (b i).re) (c : ι → ℂ) :
    ∫ v : ι → ℝ, cexp (- ∑ i, b i * (v i : ℂ) ^ 2 + ∑ i, c i * v i)
      = ∏ i, (π / b i) ^ (1 / 2 : ℂ) * cexp (c i ^ 2 / (4 * b i)) := by
  simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Complex.exp_sum, ← neg_mul]
  rw [integral_fintype_prod_eq_prod (f := fun i (v : ℝ) ↦ cexp (-b i * v ^ 2 + c i * v))]
  congr with i
  have : (-b i).re < 0 := by simpa using hb i
  convert integral_cexp_quadratic this (c i) 0 using 1 <;> simp [div_neg]

theorem integral_cexp_neg_mul_sum_add {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c : ι → ℂ) :
    ∫ v : ι → ℝ, cexp (- b * ∑ i, (v i : ℂ) ^ 2 + ∑ i, c i * v i)
      = (π / b) ^ (Fintype.card ι / 2 : ℂ) * cexp ((∑ i, c i ^ 2) / (4 * b)) := by
  simp_rw [neg_mul, Finset.mul_sum, integral_cexp_neg_sum_mul_add (fun _ ↦ hb) c]
  simp only [one_div, Finset.prod_mul_distrib, Finset.prod_const, ← cpow_nat_mul, ← Complex.exp_sum,
    Fintype.card, Finset.sum_div]
  rfl

theorem integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c : ℂ) (w : EuclideanSpace ℝ ι) :
    ∫ v : EuclideanSpace ℝ ι, cexp (- b * ‖v‖^2 + c * ⟪w, v⟫) =
      (π / b) ^ (Fintype.card ι / 2 : ℂ) * cexp (c ^ 2 * ‖w‖^2 / (4 * b)) := by
  have := (EuclideanSpace.volume_preserving_measurableEquiv ι).symm
  rw [← this.integral_comp (MeasurableEquiv.measurableEmbedding _)]
  simp only [neg_mul, Function.comp_def]
  convert integral_cexp_neg_mul_sum_add hb (fun i ↦ c * w i) using 5 with _x y
  · simp only [EuclideanSpace.measurableEquiv, MeasurableEquiv.symm_mk, MeasurableEquiv.coe_mk,
      EuclideanSpace.norm_eq, WithLp.equiv_symm_pi_apply, Real.norm_eq_abs, sq_abs, neg_mul,
      neg_inj, mul_eq_mul_left_iff]
    norm_cast
    left
    rw [sq_sqrt]
    exact Finset.sum_nonneg (fun i _hi ↦ by positivity)
  · simp [PiLp.inner_apply, EuclideanSpace.measurableEquiv, Finset.mul_sum, mul_assoc]
  · simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, mul_pow, ← Finset.mul_sum]
    congr
    norm_cast
    rw [sq_sqrt]
    exact Finset.sum_nonneg (fun i _hi ↦ by positivity)

theorem integral_cexp_neg_mul_sq_norm_add
    (hb : 0 < b.re) (c : ℂ) (w : V) :
    ∫ v : V, cexp (- b * ‖v‖^2 + c * ⟪w, v⟫) =
      (π / b) ^ (FiniteDimensional.finrank ℝ V / 2 : ℂ) * cexp (c ^ 2 * ‖w‖^2 / (4 * b)) := by
  let e := (stdOrthonormalBasis ℝ V).repr.symm
  rw [← e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding]
  convert integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    hb c (e.symm w) <;> simp [LinearIsometryEquiv.inner_map_eq_flip]

theorem integral_cexp_neg_mul_sq_norm (hb : 0 < b.re) :
    ∫ v : V, cexp (- b * ‖v‖^2) = (π / b) ^ (FiniteDimensional.finrank ℝ V / 2 : ℂ) := by
  simpa using integral_cexp_neg_mul_sq_norm_add hb 0 (0 : V)

theorem integral_rexp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) :
    ∫ v : V, rexp (- b * ‖v‖^2) = (π / b) ^ (FiniteDimensional.finrank ℝ V / 2 : ℝ) := by
  rw [← ofReal_inj]
  convert integral_cexp_neg_mul_sq_norm (show 0 < (b : ℂ).re from hb) (V := V)
  · change ofRealLI (∫ (v : V), rexp (-b * ‖v‖ ^ 2)) = ∫ (v : V), cexp (-↑b * ↑‖v‖ ^ 2)
    rw [← ofRealLI.integral_comp_comm]
    simp [ofRealLI]
  · rw [← ofReal_div, ofReal_cpow (by positivity)]
    simp

theorem _root_.fourierIntegral_gaussian_innerProductSpace' (hb : 0 < b.re) (x w : V) :
    𝓕 (fun v ↦ cexp (- b * ‖v‖^2 + 2 * π * Complex.I * ⟪x, v⟫)) w =
      (π / b) ^ (FiniteDimensional.finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * ‖x - w‖ ^ 2 / b) := by
  simp only [neg_mul, fourierIntegral_eq', ofReal_neg, ofReal_mul, ofReal_ofNat,
    smul_eq_mul, ← Complex.exp_add, real_inner_comm w]
  convert integral_cexp_neg_mul_sq_norm_add hb (2 * π * Complex.I) (x - w) using 3 with v
  · congr 1
    simp [inner_sub_left]
    ring
  · have : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
    field_simp [mul_pow]
    ring

theorem _root_.fourierIntegral_gaussian_innerProductSpace (hb : 0 < b.re) (w : V) :
    𝓕 (fun v ↦ cexp (- b * ‖v‖^2)) w =
      (π / b) ^ (FiniteDimensional.finrank ℝ V / 2 : ℂ) * cexp (-π ^ 2 * ‖w‖^2 / b) := by
  simpa using fourierIntegral_gaussian_innerProductSpace' hb 0 w

end InnerProductSpace

end GaussianFourier

section GaussianPoisson

/-! ## Poisson summation applied to the Gaussian -/

variable {E : Type*} [NormedAddCommGroup E]

/-! First we show that Gaussian-type functions have rapid decay along `cocompact ℝ`. -/

lemma rexp_neg_quadratic_isLittleO_rpow_atTop {a : ℝ} (ha : a < 0) (b s : ℝ) :
    (fun x ↦ rexp (a * x ^ 2 + b * x)) =o[atTop] (· ^ s) := by
  suffices (fun x ↦ rexp (a * x ^ 2 + b * x)) =o[atTop] (fun x ↦ rexp (-x)) by
    refine this.trans ?_
    simpa only [neg_one_mul] using isLittleO_exp_neg_mul_rpow_atTop zero_lt_one s
  rw [isLittleO_exp_comp_exp_comp]
  have : (fun x ↦ -x - (a * x ^ 2 + b * x)) = fun x ↦ x * (-a * x - (b + 1)) := by
    ext1 x; ring_nf
  rw [this]
  exact tendsto_id.atTop_mul_atTop <|
    Filter.tendsto_atTop_add_const_right _ _ <| tendsto_id.const_mul_atTop (neg_pos.mpr ha)

lemma cexp_neg_quadratic_isLittleO_rpow_atTop {a : ℂ} (ha : a.re < 0) (b : ℂ) (s : ℝ) :
    (fun x : ℝ ↦ cexp (a * x ^ 2 + b * x)) =o[atTop] (· ^ s) := by
  apply Asymptotics.IsLittleO.of_norm_left
  convert rexp_neg_quadratic_isLittleO_rpow_atTop ha b.re s with x
  simp_rw [Complex.norm_eq_abs, Complex.abs_exp, add_re, ← ofReal_pow, mul_comm (_ : ℂ) ↑(_ : ℝ),
      re_ofReal_mul, mul_comm _ (re _)]

lemma cexp_neg_quadratic_isLittleO_abs_rpow_cocompact {a : ℂ} (ha : a.re < 0) (b : ℂ) (s : ℝ) :
    (fun x : ℝ ↦ cexp (a * x ^ 2 + b * x)) =o[cocompact ℝ] (|·| ^ s) := by
  rw [cocompact_eq_atBot_atTop, isLittleO_sup]
  constructor
  · refine ((cexp_neg_quadratic_isLittleO_rpow_atTop ha (-b) s).comp_tendsto
      Filter.tendsto_neg_atBot_atTop).congr' (eventually_of_forall fun x ↦ ?_) ?_
    · simp only [neg_mul, Function.comp_apply, ofReal_neg, neg_sq, mul_neg, neg_neg]
    · refine (eventually_lt_atBot 0).mp (eventually_of_forall fun x hx ↦ ?_)
      simp only [Function.comp_apply, abs_of_neg hx]
  · refine (cexp_neg_quadratic_isLittleO_rpow_atTop ha b s).congr' EventuallyEq.rfl ?_
    refine (eventually_gt_atTop 0).mp (eventually_of_forall fun x hx ↦ ?_)
    simp_rw [abs_of_pos hx]

theorem tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact {a : ℝ} (ha : 0 < a) (s : ℝ) :
    Tendsto (fun x : ℝ => |x| ^ s * rexp (-a * x ^ 2)) (cocompact ℝ) (𝓝 0) := by
  conv in rexp _ => rw [← sq_abs]
  erw [cocompact_eq_atBot_atTop, ← comap_abs_atTop,
    @tendsto_comap'_iff _ _ _ (fun y => y ^ s * rexp (-a * y ^ 2)) _ _ _
      (mem_atTop_sets.mpr ⟨0, fun b hb => ⟨b, abs_of_nonneg hb⟩⟩)]
  exact
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg ha s).tendsto_zero_of_tendsto
      (tendsto_exp_atBot.comp <| tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr one_half_pos))
#align tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact

theorem isLittleO_exp_neg_mul_sq_cocompact {a : ℂ} (ha : 0 < a.re) (s : ℝ) :
    (fun x : ℝ => Complex.exp (-a * x ^ 2)) =o[cocompact ℝ] fun x : ℝ => |x| ^ s := by
  convert cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (?_ : (-a).re < 0) 0 s using 1
  · simp_rw [zero_mul, add_zero]
  · rwa [neg_re, neg_lt_zero]
#align is_o_exp_neg_mul_sq_cocompact isLittleO_exp_neg_mul_sq_cocompact

/-- Jacobi's theta-function transformation formula for the sum of `exp -Q(x)`, where `Q` is a
negative definite quadratic form. -/
theorem Complex.tsum_exp_neg_quadratic {a : ℂ} (ha : 0 < a.re) (b : ℂ) :
    (∑' n : ℤ, cexp (-π * a * n ^ 2 + 2 * π * b * n)) =
      1 / a ^ (1 / 2 : ℂ) * ∑' n : ℤ, cexp (-π / a * (n + I * b) ^ 2) := by
  let f : ℝ → ℂ := fun x ↦ cexp (-π * a * x ^ 2 + 2 * π * b * x)
  have hCf : Continuous f := by
    refine Complex.continuous_exp.comp (Continuous.add ?_ ?_)
    · exact continuous_const.mul (Complex.continuous_ofReal.pow 2)
    · exact continuous_const.mul Complex.continuous_ofReal
  have hFf : 𝓕 f = fun x : ℝ ↦ 1 / a ^ (1 / 2 : ℂ) * cexp (-π / a * (x + I * b) ^ 2) :=
    fourierIntegral_gaussian_pi' ha b
  have h1 : 0 < (↑π * a).re := by
    rw [re_ofReal_mul]
    exact mul_pos pi_pos ha
  have h2 : 0 < (↑π / a).re := by
    rw [div_eq_mul_inv, re_ofReal_mul, inv_re]
    refine' mul_pos pi_pos (div_pos ha <| normSq_pos.mpr _)
    contrapose! ha
    rw [ha, zero_re]
  have f_bd : f =O[cocompact ℝ] (fun x => |x| ^ (-2 : ℝ)) := by
    convert (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact ?_ _ (-2)).isBigO
    rwa [neg_mul, neg_re, neg_lt_zero]
  have Ff_bd : (𝓕 f) =O[cocompact ℝ] (fun x => |x| ^ (-2 : ℝ)) := by
    rw [hFf]
    have : ∀ (x : ℝ), -↑π / a * (↑x + I * b) ^ 2 =
        -↑π / a * x ^ 2 + (-2 * π * I * b) / a * x + π * b ^ 2 / a := by
      intro x; ring_nf; rw [I_sq]; ring
    simp_rw [this]
    conv => enter [2, x]; rw [Complex.exp_add, ← mul_assoc _ _ (Complex.exp _), mul_comm]
    refine ((cexp_neg_quadratic_isLittleO_abs_rpow_cocompact
      (?_) (-2 * ↑π * I * b / a) (-2)).isBigO.const_mul_left _).const_mul_left _
    rwa [neg_div, neg_re, neg_lt_zero]
  convert Real.tsum_eq_tsum_fourierIntegral_of_rpow_decay hCf one_lt_two f_bd Ff_bd 0 using 1
  · simp only [f, zero_add, ofReal_int_cast]
  · rw [← tsum_mul_left]
    simp only [QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one, hFf, ofReal_int_cast]

theorem Complex.tsum_exp_neg_mul_int_sq {a : ℂ} (ha : 0 < a.re) :
    (∑' n : ℤ, cexp (-π * a * (n : ℂ) ^ 2)) =
      1 / a ^ (1 / 2 : ℂ) * ∑' n : ℤ, cexp (-π / a * (n : ℂ) ^ 2) := by
  simpa only [mul_zero, zero_mul, add_zero] using Complex.tsum_exp_neg_quadratic ha 0
#align complex.tsum_exp_neg_mul_int_sq Complex.tsum_exp_neg_mul_int_sq

theorem Real.tsum_exp_neg_mul_int_sq {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, exp (-π * a * (n : ℝ) ^ 2)) =
      (1 : ℝ) / a ^ (1 / 2 : ℝ) * (∑' n : ℤ, exp (-π / a * (n : ℝ) ^ 2)) := by
  simpa only [← ofReal_inj, ofReal_tsum, ofReal_exp, ofReal_mul, ofReal_neg, ofReal_pow,
    ofReal_int_cast, ofReal_div, ofReal_one, ofReal_cpow ha.le, ofReal_ofNat, mul_zero, zero_mul,
    add_zero] using Complex.tsum_exp_neg_quadratic (by rwa [ofReal_re] : 0 < (a : ℂ).re) 0
#align real.tsum_exp_neg_mul_int_sq Real.tsum_exp_neg_mul_int_sq

end GaussianPoisson
