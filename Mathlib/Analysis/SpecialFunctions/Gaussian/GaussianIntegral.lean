/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Batteries.Tactic.Congr
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Ring.Commute
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Field
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Neighborhoods

/-!
# Gaussian integral

We prove various versions of the formula for the Gaussian integral:
* `integral_gaussian`: for real `b` we have `∫ x:ℝ, exp (-b * x^2) = √(π / b)`.
* `integral_gaussian_complex`: for complex `b` with `0 < re b` we have
  `∫ x:ℝ, exp (-b * x^2) = (π / b) ^ (1 / 2)`.
* `integral_gaussian_Ioi` and `integral_gaussian_complex_Ioi`: variants for integrals over `Ioi 0`.
* `Complex.Gamma_one_half_eq`: the formula `Γ (1 / 2) = √π`.
-/

public section

noncomputable section

open Real Set MeasureTheory Filter Asymptotics

open scoped Real Topology

open Complex hiding exp

theorem exp_neg_mul_rpow_isLittleO_exp_neg {p b : ℝ} (hb : 0 < b) (hp : 1 < p) :
    (fun x : ℝ => exp (- b * x ^ p)) =o[atTop] fun x : ℝ => exp (-x) := by
  rw [isLittleO_exp_comp_exp_comp]
  suffices Tendsto (fun x => x * (b * x ^ (p - 1) + -1)) atTop atTop by
    refine Tendsto.congr' ?_ this
    refine eventuallyEq_of_mem (Ioi_mem_atTop (0 : ℝ)) (fun x hx => ?_)
    rw [mem_Ioi] at hx
    rw [rpow_sub_one hx.ne']
    field
  apply tendsto_id.atTop_mul_atTop₀
  refine tendsto_atTop_add_const_right atTop (-1 : ℝ) ?_
  exact Tendsto.const_mul_atTop hb (tendsto_rpow_atTop (by linarith))

theorem exp_neg_mul_sq_isLittleO_exp_neg {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => exp (-b * x ^ 2)) =o[atTop] fun x : ℝ => exp (-x) := by
  simp_rw [← rpow_two]
  exact exp_neg_mul_rpow_isLittleO_exp_neg hb one_lt_two

theorem rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg (s : ℝ) {b p : ℝ} (hp : 1 < p) (hb : 0 < b) :
    (fun x : ℝ => x ^ s * exp (- b * x ^ p)) =o[atTop] fun x : ℝ => exp (-(1 / 2) * x) := by
  apply ((isBigO_refl (fun x : ℝ => x ^ s) atTop).mul_isLittleO
      (exp_neg_mul_rpow_isLittleO_exp_neg hb hp)).trans
  simpa only [mul_comm] using Real.Gamma_integrand_isLittleO s

theorem rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg {b : ℝ} (hb : 0 < b) (s : ℝ) :
    (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) =o[atTop] fun x : ℝ => exp (-(1 / 2) * x) := by
  simp_rw [← rpow_two]
  exact rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg s one_lt_two hb

theorem integrableOn_rpow_mul_exp_neg_rpow {p s : ℝ} (hs : -1 < s) (hp : 1 ≤ p) :
    IntegrableOn (fun x : ℝ => x ^ s * exp (- x ^ p)) (Ioi 0) := by
  obtain hp | hp := le_iff_lt_or_eq.mp hp
  · have h_exp : ∀ x, ContinuousAt (fun x => exp (-x)) x := fun x => continuousAt_neg.rexp
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
    constructor
    · rw [← integrableOn_Icc_iff_integrableOn_Ioc]
      refine IntegrableOn.mul_continuousOn ?_ ?_ isCompact_Icc
      · refine (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp ?_
        exact intervalIntegral.intervalIntegrable_rpow' hs
      · intro x _
        rw [← Function.comp_def (fun x => exp (-x)) (· ^ p)]
        refine ContinuousAt.comp_continuousWithinAt (h_exp _) ?_
        exact continuousWithinAt_id.rpow_const (Or.inr (le_of_lt (lt_trans zero_lt_one hp)))
    · have h_rpow : ∀ (x r : ℝ), x ∈ Ici 1 → ContinuousWithinAt (fun x => x ^ r) (Ici 1) x := by
        intro _ _ hx
        refine continuousWithinAt_id.rpow_const (Or.inl ?_)
        exact ne_of_gt (lt_of_lt_of_le zero_lt_one hx)
      refine integrable_of_isBigO_exp_neg (by simp : (0 : ℝ) < 1 / 2)
        (ContinuousOn.mul (fun x hx => h_rpow x s hx) (fun x hx => ?_)) (IsLittleO.isBigO ?_)
      · rw [← Function.comp_def (fun x => exp (-x)) (· ^ p)]
        exact ContinuousAt.comp_continuousWithinAt (h_exp _) (h_rpow x p hx)
      · convert rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg s hp (by simp : (0 : ℝ) < 1) using 3
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
    rw [← mul_assoc, mul_rpow, mul_rpow, ← rpow_mul (z := p), neg_mul, neg_mul, inv_mul_cancel₀,
      rpow_neg_one, mul_inv_cancel_left₀]
    all_goals linarith [mem_Ioi.mp hx]
  refine Integrable.const_mul ?_ _
  rw [← IntegrableOn]
  exact integrableOn_rpow_mul_exp_neg_rpow hs hp

theorem integrableOn_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) (Ioi 0) := by
  simp_rw [← rpow_two]
  exact integrableOn_rpow_mul_exp_neg_mul_rpow hs one_le_two hb

theorem integrable_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    Integrable fun x : ℝ => x ^ s * exp (-b * x ^ 2) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, integrableOn_rpow_mul_exp_neg_mul_sq hb hs⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simp only [Function.comp_def, neg_sq, neg_preimage, neg_Iio, neg_zero]
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

theorem integrable_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun x : ℝ => exp (-b * x ^ 2) := by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by simp : (-1 : ℝ) < 0)

theorem integrableOn_Ioi_exp_neg_mul_sq_iff {b : ℝ} :
    IntegrableOn (fun x : ℝ => exp (-b * x ^ 2)) (Ioi 0) ↔ 0 < b := by
  refine ⟨fun h => ?_, fun h => (integrable_exp_neg_mul_sq h).integrableOn⟩
  by_contra! hb
  have : ∫⁻ _ : ℝ in Ioi 0, 1 ≤ ∫⁻ x : ℝ in Ioi 0, ‖exp (-b * x ^ 2)‖₊ := by
    apply lintegral_mono (fun x ↦ _)
    simp only [neg_mul, ENNReal.one_le_coe_iff, ← toNNReal_one, toNNReal_le_iff_le_coe,
      Real.norm_of_nonneg (exp_pos _).le, coe_nnnorm, one_le_exp_iff, Right.nonneg_neg_iff]
    exact fun x ↦ mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg x)
  simpa using this.trans_lt h.2

theorem integrable_exp_neg_mul_sq_iff {b : ℝ} :
    (Integrable fun x : ℝ => exp (-b * x ^ 2)) ↔ 0 < b :=
  ⟨fun h => integrableOn_Ioi_exp_neg_mul_sq_iff.mp h.integrableOn, integrable_exp_neg_mul_sq⟩

theorem integrable_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun x : ℝ => x * exp (-b * x ^ 2) := by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by simp : (-1 : ℝ) < 1)

theorem norm_cexp_neg_mul_sq (b : ℂ) (x : ℝ) :
    ‖Complex.exp (-b * (x : ℂ) ^ 2)‖ = exp (-b.re * x ^ 2) := by
  rw [norm_exp, ← ofReal_pow, mul_comm (-b) _, re_ofReal_mul, neg_re, mul_comm]

theorem integrable_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
    Integrable fun x : ℝ => cexp (-b * (x : ℂ) ^ 2) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_cexp_neg_mul_sq]
  exact (integrable_exp_neg_mul_sq hb).2

theorem integrable_mul_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
    Integrable fun x : ℝ => ↑x * cexp (-b * (x : ℂ) ^ 2) := by
  refine ⟨(continuous_ofReal.mul (Complex.continuous_exp.comp ?_)).aestronglyMeasurable, ?_⟩
  · fun_prop
  have := (integrable_mul_exp_neg_mul_sq hb).hasFiniteIntegral
  rw [← hasFiniteIntegral_norm_iff] at this ⊢
  convert this
  rw [norm_mul, norm_mul, norm_cexp_neg_mul_sq b, norm_real, norm_of_nonneg (exp_pos _).le]

theorem integral_mul_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
    ∫ r : ℝ in Ioi 0, (r : ℂ) * cexp (-b * (r : ℂ) ^ 2) = (2 * b)⁻¹ := by
  have hb' : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
  have A : ∀ x : ℂ, HasDerivAt (fun x => -(2 * b)⁻¹ * cexp (-b * x ^ 2))
    (x * cexp (-b * x ^ 2)) x := by
    intro x
    convert ((hasDerivAt_pow 2 x).const_mul (-b)).cexp.const_mul (-(2 * b)⁻¹) using 1
    field
  have B : Tendsto (fun y : ℝ ↦ -(2 * b)⁻¹ * cexp (-b * (y : ℂ) ^ 2))
    atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    refine Tendsto.const_mul _ (tendsto_zero_iff_norm_tendsto_zero.mpr ?_)
    simp_rw [norm_cexp_neg_mul_sq b]
    exact tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.2 hb))
  convert integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => (A ↑x).comp_ofReal)
    (integrable_mul_cexp_neg_mul_sq hb).integrableOn B using 1
  simp only [mul_zero, ofReal_zero, zero_pow, Ne,
    not_false_iff, Complex.exp_zero, mul_one, sub_neg_eq_add, zero_add, reduceCtorEq]

set_option backward.isDefEq.respectTransparency false in
/-- The *square* of the Gaussian integral `∫ x:ℝ, exp (-b * x^2)` is equal to `π / b`. -/
theorem integral_gaussian_sq_complex {b : ℂ} (hb : 0 < b.re) :
    (∫ x : ℝ, cexp (-b * (x : ℂ) ^ 2)) ^ 2 = π / b := by
  /- We compute `(∫ exp (-b x^2))^2` as an integral over `ℝ^2`, and then make a polar change
  of coordinates. We are left with `∫ r * exp (-b r^2)`, which has been computed in
  `integral_mul_cexp_neg_mul_sq` using the fact that this function has an obvious primitive. -/
  calc
    (∫ x : ℝ, cexp (-b * (x : ℂ) ^ 2)) ^ 2 =
        ∫ p : ℝ × ℝ, cexp (-b * (p.1 : ℂ) ^ 2) * cexp (-b * (p.2 : ℂ) ^ 2) := by
      rw [pow_two, ← integral_prod_mul]; rfl
    _ = ∫ p : ℝ × ℝ, cexp (-b * ((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2)) := by
      congr
      ext1 p
      rw [← Complex.exp_add, mul_add]
    _ = ∫ p in polarCoord.target, p.1 •
        cexp (-b * ((p.1 * Complex.cos p.2) ^ 2 + (p.1 * Complex.sin p.2) ^ 2)) := by
      rw [← integral_comp_polarCoord_symm]
      simp only [polarCoord_symm_apply, ofReal_mul, ofReal_cos, ofReal_sin]
    _ = (∫ r in Ioi (0 : ℝ), r * cexp (-b * (r : ℂ) ^ 2)) * ∫ θ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul]
      congr with p : 1
      rw [mul_one]
      congr
      conv_rhs => rw [← one_mul ((p.1 : ℂ) ^ 2), ← sin_sq_add_cos_sq (p.2 : ℂ)]
      ring
    _ = ↑π / b := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
        univ_inter, real_smul, mul_one, integral_mul_cexp_neg_mul_sq hb]
      rw [volume_real_Ioo_of_le (by linarith [pi_nonneg])]
      simp
      ring

theorem integral_gaussian (b : ℝ) : ∫ x : ℝ, exp (-b * x ^ 2) = √(π / b) := by
  -- First we deal with the crazy case where `b ≤ 0`: then both sides vanish.
  rcases le_or_gt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · simpa only [not_lt, integrable_exp_neg_mul_sq_iff] using hb
  -- Assume now `b > 0`. Then both sides are non-negative and their squares agree.
  refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
  rw [← ofReal_inj, ofReal_pow, ← coe_algebraMap, RCLike.algebraMap_eq_ofReal, ← integral_ofReal,
    sq_sqrt (div_pos pi_pos hb).le, ← RCLike.algebraMap_eq_ofReal, coe_algebraMap, ofReal_div]
  convert integral_gaussian_sq_complex (by rwa [ofReal_re] : 0 < (b : ℂ).re) with _ x
  rw [ofReal_exp, ofReal_mul, ofReal_pow, ofReal_neg]

theorem continuousAt_gaussian_integral (b : ℂ) (hb : 0 < re b) :
    ContinuousAt (fun c : ℂ => ∫ x : ℝ, cexp (-c * (x : ℂ) ^ 2)) b := by
  let f : ℂ → ℝ → ℂ := fun (c : ℂ) (x : ℝ) => cexp (-c * (x : ℂ) ^ 2)
  obtain ⟨d, hd, hd'⟩ := exists_between hb
  have f_le_bd : ∀ᶠ c : ℂ in 𝓝 b, ∀ᵐ x : ℝ, ‖f c x‖ ≤ exp (-d * x ^ 2) := by
    refine eventually_of_mem ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hd') ?_
    intro c hc; filter_upwards with x
    rw [norm_cexp_neg_mul_sq]
    gcongr
    exact le_of_lt hc
  exact continuousAt_of_dominated (Eventually.of_forall (by fun_prop)) f_le_bd
    (integrable_exp_neg_mul_sq hd) (ae_of_all _ (by fun_prop))

set_option backward.isDefEq.respectTransparency false in
theorem integral_gaussian_complex {b : ℂ} (hb : 0 < re b) :
    ∫ x : ℝ, cexp (-b * (x : ℂ) ^ 2) = (π / b) ^ (1 / 2 : ℂ) := by
  have nv : ∀ {b : ℂ}, 0 < re b → b ≠ 0 := by intro b hb; contrapose! hb; rw [hb]; simp
  apply
    (convex_halfSpace_re_gt 0).isPreconnected.eq_of_sq_eq ?_ ?_ (fun c hc => ?_) (fun {c} hc => ?_)
      (by simp : 0 < re (1 : ℂ)) ?_ hb
  · -- integral is continuous
    exact continuousOn_of_forall_continuousAt continuousAt_gaussian_integral
  · -- `(π / b) ^ (1 / 2 : ℂ)` is continuous
    refine
      continuousOn_of_forall_continuousAt fun b hb =>
        (continuousAt_cpow_const (Or.inl ?_)).comp (continuousAt_const.div continuousAt_id (nv hb))
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
    · convert integral_gaussian (1 : ℝ) using 1
      rw [sqrt_eq_rpow]
    · rw [div_one]; exact pi_pos.le
  · -- squares of both sides agree
    dsimp only [Pi.pow_apply]
    rw [integral_gaussian_sq_complex hc, sq]
    conv_lhs => rw [← cpow_one (↑π / c)]
    rw [← cpow_add _ _ (div_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) (nv hc))]
    norm_num
  · -- RHS doesn't vanish
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (div_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) (nv hc))

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
    refine intervalIntegral_tendsto_integral_Iic _ ?_ tendsto_neg_atTop_atBot
    apply (integrable_cexp_neg_mul_sq hb).integrableOn
  exact tendsto_nhds_unique t2 t1

-- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for real `b`.
theorem integral_gaussian_Ioi (b : ℝ) :
    ∫ x in Ioi (0 : ℝ), exp (-b * x ^ 2) = √(π / b) / 2 := by
  rcases le_or_gt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos, zero_div]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · rwa [← IntegrableOn, integrableOn_Ioi_exp_neg_mul_sq_iff, not_lt]
  rw [← RCLike.ofReal_inj (K := ℂ), ← integral_ofReal, ← RCLike.algebraMap_eq_ofReal,
    coe_algebraMap]
  convert integral_gaussian_complex_Ioi (by rwa [ofReal_re] : 0 < (b : ℂ).re)
  · simp
  · rw [sqrt_eq_rpow, ← ofReal_div, ofReal_div, ofReal_cpow]
    · simp
    · exact (div_pos pi_pos hb).le

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian integral. -/
theorem Real.Gamma_one_half_eq : Real.Gamma (1 / 2) = √π := by
  rw [Gamma_eq_integral one_half_pos, ← integral_comp_rpow_Ioi_of_pos zero_lt_two]
  convert congr_arg (fun x : ℝ => 2 * x) (integral_gaussian_Ioi 1) using 1
  · rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    dsimp only
    have : (x ^ (2 : ℝ)) ^ (1 / (2 : ℝ) - 1) = x⁻¹ := by
      rw [← rpow_mul (le_of_lt hx)]
      norm_num
      rw [rpow_neg (le_of_lt hx), rpow_one]
    rw [smul_eq_mul, this]
    simp [field, (ne_of_lt (show 0 < x from hx)).symm]
    norm_num
  · rw [div_one, ← mul_div_assoc, mul_comm, mul_div_cancel_right₀ _ (two_ne_zero' ℝ)]

/-- The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian integral. -/
theorem Complex.Gamma_one_half_eq : Complex.Gamma (1 / 2) = (π : ℂ) ^ (1 / 2 : ℂ) := by
  convert congr_arg ((↑) : ℝ → ℂ) Real.Gamma_one_half_eq
  · simpa only [one_div, ofReal_inv, ofReal_ofNat] using Gamma_ofReal (1 / 2)
  · rw [sqrt_eq_rpow, ofReal_cpow pi_pos.le, ofReal_div, ofReal_ofNat, ofReal_one]

open scoped Nat in
/-- The special-value formula `Γ(k + 1 + 1/2) = (2 * k + 1)‼ * √π / (2 ^ (k + 1))` for half-integer
values of the gamma function in terms of `Nat.doubleFactorial`. -/
lemma Real.Gamma_nat_add_one_add_half (k : ℕ) :
    Gamma (k + 1 + 1 / 2) = (2 * k + 1 : ℕ)‼ * √π / (2 ^ (k + 1)) := by
  induction k with
  | zero => simp [-one_div, add_comm (1 : ℝ), Gamma_add_one, Gamma_one_half_eq]; ring
  | succ k ih =>
    rw [add_right_comm, Gamma_add_one (by positivity), Nat.cast_add, Nat.cast_one, ih, Nat.mul_add]
    simp
    ring

open scoped Nat in
/-- The special-value formula `Γ(k + 1/2) = (2 * k - 1)‼ * √π / (2 ^ k))` for half-integer
values of the gamma function in terms of `Nat.doubleFactorial`. -/
lemma Real.Gamma_nat_add_half (k : ℕ) :
    Gamma (k + 1 / 2) = (2 * k - 1 : ℕ)‼ * √π / (2 ^ k) := by
  cases k with
  | zero => simp [-one_div, Gamma_one_half_eq]
  | succ k => simpa [-one_div, mul_add] using Gamma_nat_add_one_add_half k
