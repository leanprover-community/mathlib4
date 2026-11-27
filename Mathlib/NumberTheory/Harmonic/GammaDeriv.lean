/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Derivative of Γ at positive integers

We prove the formula for the derivative of `Real.Gamma` at a positive integer:

`deriv Real.Gamma (n + 1) = Nat.factorial n * (-Real.eulerMascheroniConstant + harmonic n)`
-/

public section

open Nat Set Filter Topology

local notation "γ" => Real.eulerMascheroniConstant

namespace Real

/-- Explicit formula for the derivative of the Gamma function at positive integers, in terms of
harmonic numbers and the Euler-Mascheroni constant `γ`. -/
lemma deriv_Gamma_nat (n : ℕ) :
    deriv Gamma (n + 1) = n ! * (-γ + harmonic n) := by
  /- This follows from two properties of the function `f n = log (Gamma n)`:
  firstly, the elementary computation that `deriv f (n + 1) = deriv f n + 1 / n`, so that
  `deriv f n = deriv f 1 + harmonic n`; secondly, the convexity of `f` (the Bohr-Mollerup theorem),
  which shows that `deriv f n` is `log n + o(1)` as `n → ∞`. -/
  let f := log ∘ Gamma
  -- First reduce to computing derivative of `log ∘ Gamma`.
  suffices deriv (log ∘ Gamma) (n + 1) = -γ + harmonic n by
    rwa [Function.comp_def, deriv.log (differentiableAt_Gamma (fun m ↦ by linarith))
      (by positivity), Gamma_nat_eq_factorial, div_eq_iff_mul_eq (by positivity),
      mul_comm, Eq.comm] at this
  have hc : ConvexOn ℝ (Ioi 0) f := convexOn_log_Gamma
  have h_rec (x : ℝ) (hx : 0 < x) : f (x + 1) = f x + log x := by simp only [f, Function.comp_apply,
      Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne', add_comm]
  have hder {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ f x := by
    refine ((differentiableAt_Gamma ?_).log (Gamma_ne_zero ?_)) <;>
    exact fun m ↦ ne_of_gt (by linarith)
  -- Express derivative at general `n` in terms of value at `1` using recurrence relation
  have hder_rec (x : ℝ) (hx : 0 < x) : deriv f (x + 1) = deriv f x + 1 / x := by
    rw [← deriv_comp_add_const, one_div, ← deriv_log,
      ← deriv_add (hder <| by positivity) (differentiableAt_log hx.ne')]
    apply EventuallyEq.deriv_eq
    filter_upwards [eventually_gt_nhds hx] using h_rec
  have hder_nat (n : ℕ) : deriv f (n + 1) = deriv f 1 + harmonic n := by
    induction n with
    | zero => simp
    | succ n hn =>
      rw [cast_succ, hder_rec (n + 1) (by positivity), hn, harmonic_succ]
      push_cast
      ring
  suffices -deriv f 1 = γ by rw [hder_nat n, ← this, neg_neg]
  -- Use convexity to show derivative of `f` at `n + 1` is between `log n` and `log (n + 1)`
  have derivLB (n : ℕ) (hn : 0 < n) : log n ≤ deriv f (n + 1) := by
    refine (le_of_eq ?_).trans <| hc.slope_le_deriv (mem_Ioi.mpr <| Nat.cast_pos.mpr hn)
      (by positivity : _ < (_ : ℝ)) (by linarith) (hder <| by positivity)
    rw [slope_def_field, show n + 1 - n = (1 : ℝ) by ring, div_one, h_rec n (by positivity),
      add_sub_cancel_left]
  have derivUB (n : ℕ) : deriv f (n + 1) ≤ log (n + 1) := by
    refine (hc.deriv_le_slope (by positivity : (0 : ℝ) < n + 1) (by positivity : (0 : ℝ) < n + 2)
        (by linarith) (hder <| by positivity)).trans (le_of_eq ?_)
    rw [slope_def_field, show n + 2 - (n + 1) = (1 : ℝ) by ring, div_one,
      show n + 2 = (n + 1) + (1 : ℝ) by ring, h_rec (n + 1) (by positivity), add_sub_cancel_left]
  -- deduce `-deriv f 1` is bounded above + below by sequences which both tend to `γ`
  apply le_antisymm
  · apply ge_of_tendsto tendsto_harmonic_sub_log
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [le_sub_iff_add_le', ← sub_eq_add_neg, sub_le_iff_le_add', ← hder_nat]
    exact derivLB n hn
  · apply le_of_tendsto tendsto_harmonic_sub_log_add_one
    filter_upwards with n
    rw [sub_le_iff_le_add', ← sub_eq_add_neg, le_sub_iff_add_le', ← hder_nat]
    exact derivUB n


lemma hasDerivAt_Gamma_nat (n : ℕ) :
    HasDerivAt Gamma (n ! * (-γ + harmonic n)) (n + 1) :=
  (deriv_Gamma_nat n).symm ▸
    (differentiableAt_Gamma fun m ↦ (by linarith : (n : ℝ) + 1 ≠ -m)).hasDerivAt

lemma eulerMascheroniConstant_eq_neg_deriv : γ = -deriv Gamma 1 := by
  rw [show (1 : ℝ) = ↑(0 : ℕ) + 1 by simp, deriv_Gamma_nat 0]
  simp

/-- The Euler–Mascheroni constant as an integral: `γ = -∫₀^∞ log t · e^{-t} dt`. -/
lemma eulerMascheroniConstant_eq_neg_integral_log :
    γ = -∫ t in Ioi 0, log t * exp (-t) := by
  rw [eulerMascheroniConstant_eq_neg_deriv, deriv_Gamma_one_eq_integral_log]

/-- An integral representation of the Euler–Mascheroni constant, valid for any `s > 1`. -/
lemma eulerMascheroniConstant_eq_neg_integral_log_log {s : ℝ} (hs : 1 < s) :
    γ = -log (s - 1) + -((s - 1) * ∫ (t : ℝ) in Ioi 1, log (log t) * t ^ (-s)) := by
  rw [eulerMascheroniConstant_eq_neg_deriv, deriv_Gamma_one_eq_integral_log_log hs, neg_add_rev]

lemma hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1 := by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0

lemma hasDerivAt_Gamma_one_half : HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 2) := by
  have h_diff {s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ Gamma s :=
    differentiableAt_Gamma fun m ↦ ((neg_nonpos.mpr m.cast_nonneg).trans_lt hs).ne'
  have h_diff' {s : ℝ} (hs : 0 < s) : DifferentiableAt ℝ (fun s ↦ Gamma (2 * s)) s :=
    .comp (g := Gamma) _ (h_diff <| mul_pos two_pos hs) (differentiableAt_id.const_mul _)
  refine (h_diff one_half_pos).hasDerivAt.congr_deriv ?_
  -- We calculate the deriv of Gamma at 1/2 using the doubling formula, since we already know
  -- the derivative of Gamma at 1.
  calc deriv Gamma (1 / 2)
  _ = (deriv (fun s ↦ Gamma s * Gamma (s + 1 / 2)) (1 / 2)) + √π * γ := by
    rw [deriv_fun_mul, Gamma_one_half_eq,
      add_assoc, ← mul_add, deriv_comp_add_const,
      (by norm_num : 1 / 2 + 1 / 2 = (1 : ℝ)), Gamma_one, mul_one,
      eulerMascheroniConstant_eq_neg_deriv, add_neg_cancel, mul_zero, add_zero]
    · apply h_diff; simp -- s = 1
    · exact ((h_diff (by simp)).hasDerivAt.comp_add_const).differentiableAt -- s = 1
  _ = (deriv (fun s ↦ Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π) (1 / 2)) + √π * γ := by
    rw [funext Gamma_mul_Gamma_add_half]
  _ = √π * (deriv (fun s ↦ Gamma (2 * s) * 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [mul_comm √π, mul_comm √π, deriv_mul_const, add_mul]
    apply DifferentiableAt.mul
    · exact .comp (g := Gamma) _ (by apply h_diff; simp) -- s = 1
        (differentiableAt_id.const_mul _)
    · exact (differentiableAt_const _).rpow (by fun_prop) two_ne_zero
  _ = √π * (deriv (fun s ↦ Gamma (2 * s)) (1 / 2) +
              deriv (fun s : ℝ ↦ 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    rw [deriv_fun_mul]
    · simp
    · exact h_diff' one_half_pos
    · exact DifferentiableAt.rpow (by fun_prop) (by fun_prop) two_ne_zero
  _ = √π * (-2 * γ + deriv (fun s : ℝ ↦ 2 ^ (1 - 2 * s)) (1 / 2) + γ) := by
    congr 3
    change deriv (Gamma ∘ fun s ↦ 2 * s) _ = _
    rw [deriv_comp, deriv_const_mul_id, mul_one_div, div_self two_ne_zero]
    · rw [mul_comm, hasDerivAt_Gamma_one.deriv, mul_neg, neg_mul]
    · apply h_diff; simp -- s = 1
    · fun_prop
  _ = √π * (-2 * γ + -(2 * log 2) + γ) := by
    congr 3
    apply HasDerivAt.deriv
    have := HasDerivAt.rpow (hasDerivAt_const (1 / 2 : ℝ) (2 : ℝ))
      (?_ : HasDerivAt (fun s : ℝ ↦ 1 - 2 * s) (-2) (1 / 2)) two_pos
    · simpa
    simp_rw [mul_comm (2 : ℝ) _]
    apply HasDerivAt.const_sub
    exact hasDerivAt_mul_const (2 : ℝ)
  _ = -√π * (γ + 2 * log 2) := by ring

section EulerIntegral

open MeasureTheory intervalIntegral

/-- The integral `∫₀ˣ (1 - e⁻ʷ) / w dw`, auxiliary for the integral form of `γ`. -/
private noncomputable def einG (x : ℝ) : ℝ := ∫ w in (0 : ℝ)..x, (1 - exp (-w)) / w

/-- The integral `∫₀ˣ log w · e⁻ʷ dw`, auxiliary for the integral form of `γ`. -/
private noncomputable def logH (x : ℝ) : ℝ := ∫ w in (0 : ℝ)..x, log w * exp (-w)

private lemma intervalIntegrable_einG (x : ℝ) (hx : 0 ≤ x) :
    IntervalIntegrable (fun w : ℝ => (1 - exp (-w)) / w) volume 0 x := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  refine Measure.integrableOn_of_bounded (M := 1) (by simp)
    (by fun_prop : Measurable fun w : ℝ => (1 - exp (-w)) / w).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
  have h0 : 0 < w := hw.1
  have hnn : 0 ≤ 1 - exp (-w) := by
    have : exp (-w) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hle : 1 - exp (-w) ≤ w := by
    have := Real.one_sub_le_exp_neg w
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnn h0.le), div_le_one h0]
  exact hle

private lemma intervalIntegrable_logH (x : ℝ) :
    IntervalIntegrable (fun w : ℝ => log w * exp (-w)) volume 0 x :=
  intervalIntegrable_log'.mul_continuousOn
    (by fun_prop : Continuous fun w : ℝ => exp (-w)).continuousOn

private lemma hasDerivAt_einG {x : ℝ} (hx : 0 < x) : HasDerivAt einG ((1 - exp (-x)) / x) x := by
  have hnum : Continuous fun w : ℝ => 1 - exp (-w) :=
    continuous_const.sub (continuous_exp.comp continuous_neg)
  have hgc : ContinuousOn (fun w : ℝ => (1 - exp (-w)) / w) (Ioi 0) :=
    ContinuousOn.div hnum.continuousOn continuousOn_id (fun w (hw : w ∈ Ioi 0) => hw.ne')
  have hsm := hgc.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi x hx
  have hcont : ContinuousAt (fun w : ℝ => (1 - exp (-w)) / w) x :=
    hgc.continuousAt (Ioi_mem_nhds hx)
  exact integral_hasDerivAt_right (intervalIntegrable_einG x hx.le) hsm hcont

private lemma hasDerivAt_logH {x : ℝ} (hx : 0 < x) : HasDerivAt logH (log x * exp (-x)) x := by
  have hgc : ContinuousOn (fun w : ℝ => log w * exp (-w)) (Ioi 0) :=
    ContinuousOn.mul (Real.continuousOn_log.mono fun w (hw : w ∈ Ioi 0) => hw.ne')
      (continuous_exp.comp continuous_neg).continuousOn
  have hsm := hgc.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioi x hx
  have hcont : ContinuousAt (fun w : ℝ => log w * exp (-w)) x :=
    hgc.continuousAt (Ioi_mem_nhds hx)
  exact integral_hasDerivAt_right (intervalIntegrable_logH x) hsm hcont

private lemma hasDerivAt_auxD_zero {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun x => einG x - log x + exp (-x) * log x + logH x) 0 y := by
  have h1 := hasDerivAt_einG hy
  have h2 := Real.hasDerivAt_log hy.ne'
  have he : HasDerivAt (fun x : ℝ => exp (-x)) (exp (-y) * (-1)) y := (hasDerivAt_neg y).exp
  have h3 := he.mul h2
  have h4 := hasDerivAt_logH hy
  have := ((h1.sub h2).add h3).add h4
  convert this using 1
  ring

private lemma integrableOn_log_mul_exp_Ioi :
    IntegrableOn (fun t : ℝ => log t * exp (-t)) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext t; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro h; by_cases h1 : t ≤ 1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (lt_of_not_ge h1)
    · rintro (h | h)
      · exact h.1
      · exact zero_lt_one.trans h
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hi : IntervalIntegrable (fun t : ℝ => log t * exp (-t)) volume 0 1 :=
      intervalIntegrable_log'.mul_continuousOn (continuous_exp.comp continuous_neg).continuousOn
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi
  · have hmono : IntegrableOn (fun t : ℝ => t * exp (-t)) (Ioi 1) := by
      have h := Real.GammaIntegral_convergent (s := 2) two_pos
      have h2 : (fun x : ℝ => rexp (-x) * x ^ ((2 : ℝ) - 1)) = fun x => exp (-x) * x := by
        funext x; norm_num
      rw [h2] at h
      exact (h.mono_set (fun t ht => (show (0 : ℝ) < t from zero_lt_one.trans ht))).congr_fun_ae
        (Filter.Eventually.of_forall fun t => by simp only [mul_comm])
    refine Integrable.mono' hmono.integrable ?_ ?_
    · exact (measurable_log.mul
        (continuous_exp.comp continuous_neg).measurable).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have h1 : (1 : ℝ) < t := ht
      have hl : 0 ≤ log t := Real.log_nonneg h1.le
      have he : 0 < exp (-t) := exp_pos _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hl he.le)]
      exact mul_le_mul_of_nonneg_right (Real.log_le_self (by linarith)) he.le

private lemma tendsto_einG_zero : Tendsto einG (𝓝[>] 0) (𝓝 0) := by
  have hnum : IntegrableOn (fun w : ℝ => (1 - exp (-w)) / w) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (intervalIntegrable_einG 1 zero_le_one)
  have hc : ContinuousOn einG (uIcc 0 1) := continuousOn_primitive_interval hnum
  have hmem : uIcc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [uIcc_of_le zero_le_one]; exact Icc_mem_nhdsGT zero_lt_one
  have h := (hc 0 (left_mem_uIcc)).tendsto.mono_left (nhdsWithin_le_of_mem hmem)
  have h0 : einG 0 = 0 := by simp [einG]
  rw [h0] at h
  exact h

private lemma tendsto_logH_zero : Tendsto logH (𝓝[>] 0) (𝓝 0) := by
  have hi : IntegrableOn (fun w : ℝ => log w * exp (-w)) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp (intervalIntegrable_logH 1)
  have hc : ContinuousOn logH (uIcc 0 1) := continuousOn_primitive_interval hi
  have hmem : uIcc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := by
    rw [uIcc_of_le zero_le_one]; exact Icc_mem_nhdsGT zero_lt_one
  have h := (hc 0 (left_mem_uIcc)).tendsto.mono_left (nhdsWithin_le_of_mem hmem)
  have h0 : logH 0 = 0 := by simp [logH]
  rw [h0] at h
  exact h

private lemma tendsto_exp_sub_one_mul_log_zero :
    Tendsto (fun ε : ℝ => (exp (-ε) - 1) * log ε) (𝓝[>] 0) (𝓝 0) := by
  have hml : Tendsto (fun ε : ℝ => ε * log ε) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_mul_log.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have hA : Tendsto (fun ε : ℝ => 2 * |ε * log ε|) (𝓝[>] 0) (𝓝 0) := by
    have := (hml.abs).const_mul 2
    simpa using this
  refine squeeze_zero_norm' ?_ hA
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
  have hε0 : 0 < ε := hε.1
  have hb : |exp (-ε) - 1| ≤ 2 * ε := by
    have h := Real.abs_exp_sub_one_le (x := -ε) (by rw [abs_neg, abs_of_pos hε0]; linarith [hε.2])
    rwa [abs_neg, abs_of_pos hε0] at h
  rw [Real.norm_eq_abs, abs_mul]
  calc |exp (-ε) - 1| * |log ε| ≤ (2 * ε) * |log ε| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ = 2 * |ε * log ε| := by rw [abs_mul, abs_of_pos hε0]; ring

private noncomputable def auxD (x : ℝ) : ℝ := einG x - log x + exp (-x) * log x + logH x

private lemma auxD_const {ε x : ℝ} (hε : 0 < ε) (hεx : ε < x) : auxD x = auxD ε := by
  have hcons := constant_of_has_deriv_right_zero (f := auxD) (a := ε) (b := x)
    (fun y hy => (hasDerivAt_auxD_zero (by linarith [hy.1])).continuousAt.continuousWithinAt)
    (fun y hy => (hasDerivAt_auxD_zero (by linarith [hy.1])).hasDerivWithinAt)
  exact hcons x ⟨hεx.le, le_rfl⟩

private lemma auxD_eq_zero {x : ℝ} (hx : 0 < x) : auxD x = 0 := by
  have hD0 : Tendsto auxD (𝓝[>] 0) (𝓝 0) := by
    have heq : auxD = fun ε => einG ε + (exp (-ε) - 1) * log ε + logH ε := by
      funext ε; simp only [auxD]; ring
    rw [heq]
    have := (tendsto_einG_zero.add tendsto_exp_sub_one_mul_log_zero).add tendsto_logH_zero
    simpa using this
  have ht : Tendsto auxD (𝓝[>] 0) (𝓝 (auxD x)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT hx] with ε hε
      exact auxD_const hε.1 hε.2)
  exact (tendsto_nhds_unique hD0 ht).symm

private lemma tendsto_exp_neg_mul_log_atTop :
    Tendsto (fun x : ℝ => exp (-x) * log x) atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => x * exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop 1] with x hx
    exact mul_nonneg (exp_pos _).le (Real.log_nonneg hx)
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have := mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith : (0 : ℝ) ≤ x))
      (exp_pos (-x)).le
    linarith [mul_comm x (exp (-x))]

/-- The integral form of the Euler–Mascheroni constant:
`∫₀ˣ (1 - e⁻ʷ) / w dw - log x → γ` as `x → ∞`. -/
theorem tendsto_integral_one_sub_exp_div_sub_log_atTop :
    Tendsto (fun x : ℝ => (∫ w in (0 : ℝ)..x, (1 - exp (-w)) / w) - log x) atTop (𝓝 γ) := by
  have hI : ∫ t in Ioi (0 : ℝ), log t * exp (-t) = -γ := by
    rw [eulerMascheroniConstant_eq_neg_integral_log]; ring
  have hH : Tendsto logH atTop (𝓝 (-γ)) := by
    rw [← hI]
    exact intervalIntegral_tendsto_integral_Ioi 0 integrableOn_log_mul_exp_Ioi tendsto_id
  have hev : ∀ᶠ x in atTop, (∫ w in (0 : ℝ)..x, (1 - exp (-w)) / w) - log x =
      -(exp (-x) * log x) - logH x := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    have := auxD_eq_zero hx
    simp only [auxD, einG] at this
    linarith
  have hT : Tendsto (fun x : ℝ => -(exp (-x) * log x) - logH x) atTop
      (𝓝 (-0 - -γ)) :=
    (tendsto_exp_neg_mul_log_atTop.neg).sub hH
  have hT' : Tendsto (fun x : ℝ => -(exp (-x) * log x) - logH x) atTop (𝓝 γ) := by
    convert hT using 2; ring
  exact hT'.congr' (hev.mono fun x hx => hx.symm)

end EulerIntegral

end Real

namespace Complex

open scoped Real

private lemma HasDerivAt.complex_of_real {f : ℂ → ℂ} {g : ℝ → ℝ} {g' s : ℝ}
    (hf : DifferentiableAt ℂ f s) (hg : HasDerivAt g g' s) (hfg : ∀ s : ℝ, f ↑s = ↑(g s)) :
    HasDerivAt f ↑g' s := by
  refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
  rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv

lemma differentiableAt_Gamma_nat_add_one (n : ℕ) :
    DifferentiableAt ℂ Gamma (n + 1) := by
  refine differentiableAt_Gamma _ (fun m ↦ ?_)
  simp only [Ne, ← ofReal_natCast, ← ofReal_one, ← ofReal_add, ← ofReal_neg, ofReal_inj,
    eq_neg_iff_add_eq_zero]
  positivity

lemma hasDerivAt_Gamma_nat (n : ℕ) :
    HasDerivAt Gamma (n ! * (-γ + harmonic n)) (n + 1) := by
  exact_mod_cast HasDerivAt.complex_of_real
    (by exact_mod_cast differentiableAt_Gamma_nat_add_one n)
    (Real.hasDerivAt_Gamma_nat n) Gamma_ofReal

/-- Explicit formula for the derivative of the complex Gamma function at positive integers, in
terms of harmonic numbers and the Euler-Mascheroni constant `γ`. -/
lemma deriv_Gamma_nat (n : ℕ) :
    deriv Gamma (n + 1) = n ! * (-γ + harmonic n) :=
  (hasDerivAt_Gamma_nat n).deriv

lemma hasDerivAt_Gamma_one : HasDerivAt Gamma (-γ) 1 := by
  simpa only [factorial_zero, cast_one, harmonic_zero, Rat.cast_zero, add_zero, mul_neg, one_mul,
    cast_zero, zero_add] using hasDerivAt_Gamma_nat 0

lemma hasDerivAt_Gamma_one_half : HasDerivAt Gamma (-√π * (γ + 2 * log 2)) (1 / 2) := by
  have := HasDerivAt.complex_of_real
    (differentiableAt_Gamma _ ?_) Real.hasDerivAt_Gamma_one_half Gamma_ofReal
  · simpa only [neg_mul, one_div, ofReal_neg, ofReal_mul, ofReal_add, ofReal_ofNat, ofNat_log,
      ofReal_inv] using this
  · intro m
    rw [← ofReal_natCast, ← ofReal_neg, ne_eq, ofReal_inj]
    exact ((neg_nonpos.mpr m.cast_nonneg).trans_lt one_half_pos).ne'

lemma hasDerivAt_Gammaℂ_one : HasDerivAt Gammaℂ (-(γ + log (2 * π)) / π) 1 := by
  let f (s : ℂ) : ℂ := 2 * (2 * π) ^ (-s)
  have : HasDerivAt (fun s : ℂ ↦ 2 * (2 * π : ℂ) ^ (-s)) (-log (2 * π) / π) 1 := by
    have := (hasDerivAt_neg' (1 : ℂ)).const_cpow (c := 2 * π)
      (Or.inl (mod_cast Real.two_pi_pos.ne'))
    refine (this.const_mul 2).congr_deriv ?_
    rw [mul_neg_one, mul_neg, cpow_neg_one, ← div_eq_inv_mul, ← mul_div_assoc,
      mul_div_mul_left _ _ two_ne_zero, neg_div]
  have := this.mul hasDerivAt_Gamma_one
  rwa [Gamma_one, mul_one, cpow_neg_one, ← div_eq_mul_inv, ← div_div, div_self two_ne_zero,
    mul_comm (1 / _), mul_one_div, ← _root_.add_div, ← neg_add, add_comm] at this

lemma hasDerivAt_Gammaℝ_one : HasDerivAt Gammaℝ (-(γ + log (4 * π)) / 2) 1 := by
  let f (s : ℂ) : ℂ := π ^ (-s / 2)
  let g (s : ℂ) : ℂ := Gamma (s / 2)
  have aux : (π : ℂ) ^ (1 / 2 : ℂ) = ↑√π := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le, ofReal_div, ofReal_one, ofReal_ofNat]
  have aux2 : (√π : ℂ) ≠ 0 := by rw [ofReal_ne_zero]; positivity
  have hf : HasDerivAt f (-log π / 2 / √π) 1 := by
    have := ((hasDerivAt_neg (1 : ℂ)).div_const 2).const_cpow (c := π) (Or.inr (by simp))
    refine this.congr_deriv ?_
    rw [mul_assoc, ← mul_div_assoc, mul_neg_one, neg_div, cpow_neg, ← div_eq_inv_mul, aux]
  have hg : HasDerivAt g (-√π * (γ + 2 * log 2) / 2) 1 := by
    have := hasDerivAt_Gamma_one_half.comp 1 (?_ : HasDerivAt (fun s : ℂ ↦ s / 2) (1 / 2) 1)
    · rwa [mul_one_div] at this
    · exact (hasDerivAt_id _).div_const _
  refine HasDerivAt.congr_deriv (hf.mul hg) ?_
  simp only [f]
  rw [Gamma_one_half_eq, aux, div_mul_cancel₀ _ aux2, neg_div _ (1 : ℂ), cpow_neg, aux,
    mul_div_assoc, ← mul_assoc, mul_neg, inv_mul_cancel₀ aux2, neg_one_mul, ← neg_div,
    ← _root_.add_div, ← neg_add, add_comm, add_assoc, ← ofReal_log Real.pi_pos.le, ← ofReal_ofNat,
    ← ofReal_log zero_le_two,
    ← ofReal_mul, ← Nat.cast_ofNat (R := ℝ), ← Real.log_pow, ← ofReal_add,
    ← Real.log_mul (by positivity) (by positivity),
    Nat.cast_ofNat, ofReal_ofNat, ofReal_log (by positivity)]
  norm_num

end Complex
