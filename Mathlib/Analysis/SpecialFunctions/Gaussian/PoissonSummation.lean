/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Poisson summation applied to the Gaussian

In `Real.tsum_exp_neg_mul_int_sq` and `Complex.tsum_exp_neg_mul_int_sq`, we use Poisson summation
to prove the identity

`∑' (n : ℤ), exp (-π * a * n ^ 2) = 1 / a ^ (1 / 2) * ∑' (n : ℤ), exp (-π / a * n ^ 2)`

for positive real `a`, or complex `a` with positive real part. (See also
`NumberTheory.ModularForms.JacobiTheta`.)
-/

public section

open Real Set MeasureTheory Filter Asymptotics intervalIntegral

open scoped Real Topology FourierTransform RealInnerProductSpace

open Complex hiding exp continuous_exp

noncomputable section

section GaussianPoisson

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
  exact tendsto_id.atTop_mul_atTop₀ <| tendsto_atTop_add_const_right _ _ <|
    tendsto_id.const_mul_atTop (neg_pos.mpr ha)

lemma cexp_neg_quadratic_isLittleO_rpow_atTop {a : ℂ} (ha : a.re < 0) (b : ℂ) (s : ℝ) :
    (fun x : ℝ ↦ cexp (a * x ^ 2 + b * x)) =o[atTop] (· ^ s) := by
  apply Asymptotics.IsLittleO.of_norm_left
  convert rexp_neg_quadratic_isLittleO_rpow_atTop ha b.re s with x
  simp_rw [Complex.norm_exp, add_re, ← ofReal_pow, mul_comm (_ : ℂ) ↑(_ : ℝ),
      re_ofReal_mul, mul_comm _ (re _)]

lemma cexp_neg_quadratic_isLittleO_abs_rpow_cocompact {a : ℂ} (ha : a.re < 0) (b : ℂ) (s : ℝ) :
    (fun x : ℝ ↦ cexp (a * x ^ 2 + b * x)) =o[cocompact ℝ] (|·| ^ s) := by
  rw [cocompact_eq_atBot_atTop, isLittleO_sup]
  constructor
  · refine ((cexp_neg_quadratic_isLittleO_rpow_atTop ha (-b) s).comp_tendsto
      Filter.tendsto_neg_atBot_atTop).congr' (Eventually.of_forall fun x ↦ by simp) ?_
    · refine (eventually_lt_atBot 0).mp (Eventually.of_forall fun x hx ↦ ?_)
      simp only [Function.comp_apply, abs_of_neg hx]
  · refine (cexp_neg_quadratic_isLittleO_rpow_atTop ha b s).congr' EventuallyEq.rfl ?_
    refine (eventually_gt_atTop 0).mp (Eventually.of_forall fun x hx ↦ ?_)
    simp_rw [abs_of_pos hx]

theorem tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact {a : ℝ} (ha : 0 < a) (s : ℝ) :
    Tendsto (fun x : ℝ => |x| ^ s * rexp (-a * x ^ 2)) (cocompact ℝ) (𝓝 0) := by
  conv in rexp _ => rw [← sq_abs]
  rw [cocompact_eq_atBot_atTop, ← comap_abs_atTop]
  erw [tendsto_comap'_iff (m := fun y => y ^ s * rexp (-a * y ^ 2))
      (mem_atTop_sets.mpr ⟨0, fun b hb => ⟨b, abs_of_nonneg hb⟩⟩)]
  exact
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg ha s).tendsto_zero_of_tendsto
      (tendsto_exp_atBot.comp <| tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr one_half_pos))

theorem isLittleO_exp_neg_mul_sq_cocompact {a : ℂ} (ha : 0 < a.re) (s : ℝ) :
    (fun x : ℝ => Complex.exp (-a * x ^ 2)) =o[cocompact ℝ] fun x : ℝ => |x| ^ s := by
  convert cexp_neg_quadratic_isLittleO_abs_rpow_cocompact (?_ : (-a).re < 0) 0 s using 1
  · simp_rw [zero_mul, add_zero]
  · rwa [neg_re, neg_lt_zero]

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
    fourier_gaussian_pi' ha b
  have h1 : 0 < (↑π * a).re := by
    rw [re_ofReal_mul]
    exact mul_pos pi_pos ha
  have h2 : 0 < (↑π / a).re := by
    rw [div_eq_mul_inv, re_ofReal_mul, inv_re]
    refine mul_pos pi_pos (div_pos ha <| normSq_pos.mpr ?_)
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
  convert Real.tsum_eq_tsum_fourier_of_rpow_decay hCf one_lt_two f_bd Ff_bd 0 using 1
  · simp only [f, zero_add, ofReal_intCast]
  · rw [← tsum_mul_left]
    simp only [QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one, hFf, ofReal_intCast]

theorem Complex.tsum_exp_neg_mul_int_sq {a : ℂ} (ha : 0 < a.re) :
    (∑' n : ℤ, cexp (-π * a * (n : ℂ) ^ 2)) =
      1 / a ^ (1 / 2 : ℂ) * ∑' n : ℤ, cexp (-π / a * (n : ℂ) ^ 2) := by
  simpa only [mul_zero, zero_mul, add_zero] using Complex.tsum_exp_neg_quadratic ha 0

theorem Real.tsum_exp_neg_mul_int_sq {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, exp (-π * a * (n : ℝ) ^ 2)) =
      (1 : ℝ) / a ^ (1 / 2 : ℝ) * (∑' n : ℤ, exp (-π / a * (n : ℝ) ^ 2)) := by
  simpa only [← ofReal_inj, ofReal_tsum, ofReal_exp, ofReal_mul, ofReal_neg, ofReal_pow,
    ofReal_intCast, ofReal_div, ofReal_one, ofReal_cpow ha.le, ofReal_ofNat, mul_zero, zero_mul,
    add_zero] using Complex.tsum_exp_neg_quadratic (by rwa [ofReal_re] : 0 < (a : ℂ).re) 0

end GaussianPoisson
