/-
Copyright (c) 2026 Tianyu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tianyu (forxhunter)
-/
module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The Mittag-Leffler expansion of the Beta function

The Beta function `Β(u, v)`, viewed as a function of `u` at fixed `v`, is meromorphic with
simple poles at `u = 0, -1, -2, …`. On the domain `0 < re u`, `0 < re v` of the Euler
integral this is witnessed by the absolutely convergent partial-fraction (Mittag-Leffler)
expansion

`Β(u, v) = ∑' n : ℕ, Ring.choose (n - v) n / (n + u)`,

where `Ring.choose (n - v) n = (1 - v)⁽ⁿ⁾ / n!` (a rising factorial) is the `n`-th
coefficient of the binomial series of `x ↦ (1 - x) ^ (v - 1)`. The proof is elementary:
expand `(1 - x) ^ (v - 1)` in the Euler integral by the binomial series and integrate term
by term.

The absolute convergence rests on a growth bound for the coefficients which is proved
without any Stirling-type asymptotics (Mathlib currently has no complex Stirling formula
and no `Γ`-ratio asymptotics): applying `Real.log (1 + u) ≤ u` to each factor of
`Ring.choose (t + n) n = ∏ k < n, (t + k + 1) / (k + 1)` and summing against the harmonic
bounds `Real.log (n + 1) ≤ harmonic n` and `∑ k < n, 1 / (k + 1) ^ 2 ≤ 2` yields
`‖Ring.choose (t + n) n‖ ≤ exp (normSq t) * (n + 1) ^ t.re`, which decays like a `p`-series
of exponent `t.re` as soon as `t.re < 0`.

## Main results

* `Ring.choose_add_natCast_eq_prod_range`: `Ring.choose (t + n) n` as the finite product
  `∏ k < n, (t + k + 1) / (k + 1)` in a field of characteristic zero.
* `Complex.norm_ringChoose_add_natCast_le`: the Stirling-free growth bound
  `‖Ring.choose (t + n) n‖ ≤ Real.exp (normSq t) * (n + 1) ^ t.re` for `t.re ≤ 0`.
* `Complex.summable_norm_ringChoose_div`: absolute convergence of the pole series.
* `Complex.hasSum_ringChoose_mul_pow`: the binomial series
  `(1 - x) ^ (-t - 1) = ∑' n, Ring.choose (t + n) n * x ^ n` in `HasSum` form.
* `integral_Ioo_cpow`, `integral_Ioo_rpow`: `∫ x in Ioo 0 1, x ^ w = 1 / (w + 1)`.
* `Complex.hasSum_betaIntegral`: the Mittag-Leffler expansion of `Complex.betaIntegral`.

## Tags

beta function, Mittag-Leffler, partial fraction, binomial series, pole expansion
-/

@[expose] public section

open scoped Real

/-! ### `Ring.choose` along a shifted diagonal, as a finite product -/

/-- `Ring.choose (t + n) n = ∏ k < n, (t + k + 1) / (k + 1)`, the rising-factorial form
`(t + 1)⁽ⁿ⁾ / n!` of the binomial coefficient with entries distributed into the product.
This form gives access to the size of `Ring.choose (t + n) n` one factor at a time. -/
theorem Ring.choose_add_natCast_eq_prod_range {K : Type*} [Field K] [CharZero K]
    (t : K) (n : ℕ) :
    Ring.choose (t + n) n = ∏ k ∈ Finset.range n, (t + (k + 1)) / (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : ((n : K) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hstep : ((n : K) + 1) * Ring.choose (t + (n : K) + 1) (n + 1)
        = (t + (n : K) + 1) * Ring.choose (t + (n : K)) n := by
      have h := Ring.choose_add_smul_choose (t + (n : K)) n 1
      rw [Nat.choose_one_right, nsmul_eq_mul, Nat.cast_one, Ring.choose_one_right] at h
      push_cast at h
      linear_combination h
    rw [Finset.prod_range_succ, ← ih]
    push_cast
    rw [← add_assoc, ← mul_div_assoc, eq_div_iff hne]
    linear_combination hstep

/-! ### Elementary harmonic estimates -/

/-- `log (n + 1) ≤ Hₙ`, restated as a `Finset.range` sum. -/
private theorem log_le_sum_inv_succ (n : ℕ) :
    Real.log ((n : ℝ) + 1) ≤ ∑ k ∈ Finset.range n, ((k : ℝ) + 1)⁻¹ := by
  have h := log_add_one_le_harmonic n
  have hcast : ((harmonic n : ℚ) : ℝ) = ∑ k ∈ Finset.range n, ((k : ℝ) + 1)⁻¹ := by
    rw [show harmonic n = ∑ i ∈ Finset.range n, ((i + 1 : ℕ) : ℚ)⁻¹ from rfl]
    push_cast
    rfl
  rw [hcast] at h
  push_cast at h
  exact h

/-- `∑ k < n, 1 / (k + 1) ^ 2 ≤ 2 - 2 / (n + 1)`, by the telescoping bound
`1 / (k + 1) ^ 2 ≤ 2 / (k + 1) - 2 / (k + 2)`, which holds for every `k ≥ 0` (unlike the
sharper `1 / (k + 1) ^ 2 ≤ 1 / (k + 1) - 1 / (k + 2)`, which is false). -/
private theorem sum_inv_succ_sq_le (n : ℕ) :
    ∑ k ∈ Finset.range n, (((k : ℝ) + 1) ^ 2)⁻¹ ≤ 2 - 2 * ((n : ℝ) + 1)⁻¹ := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have key : 2 * ((n : ℝ) + 1)⁻¹ - 2 * ((n : ℝ) + 2)⁻¹ - (((n : ℝ) + 1) ^ 2)⁻¹
        = (n : ℝ) / (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by
      field_simp
      ring
    have hkey : 0 ≤ 2 * ((n : ℝ) + 1)⁻¹ - 2 * ((n : ℝ) + 2)⁻¹ - (((n : ℝ) + 1) ^ 2)⁻¹ := by
      rw [key]; positivity
    have hcast : ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 := by ring
    rw [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one, hcast]
    linarith

/-! ### Elementary power integrals over `Ioo 0 1` -/

/-- `∫ x in Ioo 0 1, x ^ w = 1 / (w + 1)` for complex `w` with `-1 < re w`. -/
theorem integral_Ioo_cpow {w : ℂ} (hw : -1 < w.re) :
    ∫ x in Set.Ioo (0 : ℝ) 1, (x : ℂ) ^ w = 1 / (w + 1) := by
  have hw1 : w + 1 ≠ 0 := by
    intro hc
    have hre : w.re + 1 = 0 := by
      have := congrArg Complex.re hc
      simpa using this
    linarith
  have h := integral_cpow (a := (0 : ℝ)) (b := 1) (r := w) (Or.inl hw)
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  rw [h, Complex.ofReal_one, Complex.ofReal_zero, Complex.one_cpow,
    Complex.zero_cpow hw1, sub_zero]

/-- `∫ x in Ioo 0 1, x ^ r = 1 / (r + 1)` for real `r > -1`. -/
theorem integral_Ioo_rpow {r : ℝ} (hr : -1 < r) :
    ∫ x in Set.Ioo (0 : ℝ) 1, x ^ r = 1 / (r + 1) := by
  have hr1 : r + 1 ≠ 0 := by intro hc; linarith
  have h := integral_rpow (a := (0 : ℝ)) (b := 1) (r := r) (Or.inl hr)
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo] at h
  rw [h, Real.one_rpow, Real.zero_rpow hr1, sub_zero]

namespace Complex

/-! ### A Stirling-free growth bound for `Ring.choose (t + n) n` -/

/-- The single inequality behind the growth bound: `log (1 + u) ≤ u` applied to
`‖1 + t / c‖ ^ 2 = 1 + 2 * t.re / c + normSq t / c ^ 2`. -/
private theorem log_norm_add_div_le {t : ℂ} {c : ℝ} (hc : 0 < c) (h : t + (c : ℂ) ≠ 0) :
    Real.log ‖(t + (c : ℂ)) / (c : ℂ)‖ ≤ t.re / c + normSq t / (2 * c ^ 2) := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hnz : (t + (c : ℂ)) / (c : ℂ) ≠ 0 := div_ne_zero h hc0
  have hpos : (0 : ℝ) < ‖(t + (c : ℂ)) / (c : ℂ)‖ := norm_pos_iff.mpr hnz
  have hnormSq : normSq (t + (c : ℂ)) = c ^ 2 + 2 * c * t.re + normSq t := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero]
    ring
  have hsq : ‖(t + (c : ℂ)) / (c : ℂ)‖ ^ 2 = 1 + (2 * t.re / c + normSq t / c ^ 2) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_div, Complex.normSq_ofReal, hnormSq]
    field_simp
    ring
  have hargpos : (0 : ℝ) < 1 + (2 * t.re / c + normSq t / c ^ 2) := by
    rw [← hsq]; positivity
  have hlog : Real.log (‖(t + (c : ℂ)) / (c : ℂ)‖ ^ 2) ≤ 2 * t.re / c + normSq t / c ^ 2 := by
    rw [hsq]
    have := Real.log_le_sub_one_of_pos hargpos
    linarith
  rw [Real.log_pow] at hlog
  have h2 : (2 : ℝ) * Real.log ‖(t + (c : ℂ)) / (c : ℂ)‖
      ≤ 2 * t.re / c + normSq t / c ^ 2 := by
    simpa using hlog
  have hEq : t.re / c + normSq t / (2 * c ^ 2) = (2 * t.re / c + normSq t / c ^ 2) / 2 := by
    ring
  rw [hEq]
  linarith

/-- `log_norm_add_div_le` at the shifts `c = k + 1` appearing in
`Ring.choose_add_natCast_eq_prod_range`. -/
private theorem log_norm_factor_le (t : ℂ) (k : ℕ) (h : t + ((k : ℂ) + 1) ≠ 0) :
    Real.log ‖(t + ((k : ℂ) + 1)) / ((k : ℂ) + 1)‖
      ≤ t.re / ((k : ℝ) + 1) + normSq t / (2 * ((k : ℝ) + 1) ^ 2) := by
  have hc : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hcast : ((((k : ℝ) + 1 : ℝ)) : ℂ) = (k : ℂ) + 1 := by push_cast; ring
  rw [← hcast] at h ⊢
  exact log_norm_add_div_le hc h

/-- **A Stirling-free growth bound**: `‖Ring.choose (t + n) n‖ ≤ exp (normSq t) * (n + 1) ^ t.re`
for `t.re ≤ 0`. Writing `Ring.choose (t + n) n = (t + 1)⁽ⁿ⁾ / n!` as a product, the proof
is `Real.log (1 + u) ≤ u` on each factor, summed against `Real.log (n + 1) ≤ harmonic n` and
`∑ k < n, 1 / (k + 1) ^ 2 ≤ 2`; no Stirling asymptotics are needed. -/
theorem norm_ringChoose_add_natCast_le {t : ℂ} (ht : t.re ≤ 0) (n : ℕ) :
    ‖Ring.choose (t + (n : ℂ)) n‖ ≤ Real.exp (normSq t) * ((n : ℝ) + 1) ^ t.re := by
  have hbase : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Ring.choose_add_natCast_eq_prod_range]
  by_cases hzero : ∃ k ∈ Finset.range n, t + ((k : ℂ) + 1) = 0
  · obtain ⟨k, hk, hk0⟩ := hzero
    have hw : ∏ k ∈ Finset.range n, (t + ((k : ℂ) + 1)) / ((k : ℂ) + 1) = 0 := by
      refine Finset.prod_eq_zero hk ?_
      rw [hk0, zero_div]
    rw [hw, norm_zero]
    positivity
  · push Not at hzero
    have hfac : ∀ k ∈ Finset.range n, (t + ((k : ℂ) + 1)) / ((k : ℂ) + 1) ≠ 0 := fun k hk =>
      div_ne_zero (hzero k hk) (Nat.cast_add_one_ne_zero k)
    have hnormprod : ‖∏ k ∈ Finset.range n, (t + ((k : ℂ) + 1)) / ((k : ℂ) + 1)‖
        = ∏ k ∈ Finset.range n, ‖(t + ((k : ℂ) + 1)) / ((k : ℂ) + 1)‖ :=
      norm_prod _ _
    have hwpos : 0 < ‖∏ k ∈ Finset.range n, (t + ((k : ℂ) + 1)) / ((k : ℂ) + 1)‖ := by
      rw [hnormprod]
      exact Finset.prod_pos fun k hk => norm_pos_iff.mpr (hfac k hk)
    have hlogsum : Real.log ‖∏ k ∈ Finset.range n, (t + ((k : ℂ) + 1)) / ((k : ℂ) + 1)‖
        = ∑ k ∈ Finset.range n, Real.log ‖(t + ((k : ℂ) + 1)) / ((k : ℂ) + 1)‖ := by
      rw [hnormprod, Real.log_prod]
      exact fun k hk => norm_ne_zero_iff.mpr (hfac k hk)
    have hterm : ∑ k ∈ Finset.range n, Real.log ‖(t + ((k : ℂ) + 1)) / ((k : ℂ) + 1)‖
        ≤ ∑ k ∈ Finset.range n,
            (t.re * ((k : ℝ) + 1)⁻¹ + normSq t / 2 * ((((k : ℝ) + 1) ^ 2)⁻¹)) := by
      refine Finset.sum_le_sum fun k hk => ?_
      have h := log_norm_factor_le t k (hzero k hk)
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hrw : t.re / ((k : ℝ) + 1) + normSq t / (2 * ((k : ℝ) + 1) ^ 2)
          = t.re * ((k : ℝ) + 1)⁻¹ + normSq t / 2 * ((((k : ℝ) + 1) ^ 2)⁻¹) := by
        field_simp
      rw [hrw] at h
      exact h
    have hsplit : ∑ k ∈ Finset.range n,
          (t.re * ((k : ℝ) + 1)⁻¹ + normSq t / 2 * ((((k : ℝ) + 1) ^ 2)⁻¹))
        = t.re * (∑ k ∈ Finset.range n, ((k : ℝ) + 1)⁻¹)
          + normSq t / 2 * (∑ k ∈ Finset.range n, (((k : ℝ) + 1) ^ 2)⁻¹) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hharm : t.re * (∑ k ∈ Finset.range n, ((k : ℝ) + 1)⁻¹)
        ≤ t.re * Real.log ((n : ℝ) + 1) := by
      have hh := log_le_sum_inv_succ n
      nlinarith [mul_nonneg (neg_nonneg.mpr ht) (sub_nonneg.mpr hh)]
    have hsq2 : normSq t / 2 * (∑ k ∈ Finset.range n, (((k : ℝ) + 1) ^ 2)⁻¹) ≤ normSq t := by
      have hs2 : (∑ k ∈ Finset.range n, (((k : ℝ) + 1) ^ 2)⁻¹) ≤ 2 := by
        have hle := sum_inv_succ_sq_le n
        have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
        linarith
      have hns : (0 : ℝ) ≤ normSq t / 2 := by
        have := Complex.normSq_nonneg t
        linarith
      have := mul_le_mul_of_nonneg_left hs2 hns
      linarith
    have hfinal : Real.log ‖∏ k ∈ Finset.range n, (t + ((k : ℂ) + 1)) / ((k : ℂ) + 1)‖
        ≤ t.re * Real.log ((n : ℝ) + 1) + normSq t := by
      rw [hlogsum]
      calc ∑ k ∈ Finset.range n, Real.log ‖(t + ((k : ℂ) + 1)) / ((k : ℂ) + 1)‖
          ≤ ∑ k ∈ Finset.range n,
              (t.re * ((k : ℝ) + 1)⁻¹ + normSq t / 2 * ((((k : ℝ) + 1) ^ 2)⁻¹)) := hterm
        _ = t.re * (∑ k ∈ Finset.range n, ((k : ℝ) + 1)⁻¹)
              + normSq t / 2 * (∑ k ∈ Finset.range n, (((k : ℝ) + 1) ^ 2)⁻¹) := hsplit
        _ ≤ t.re * Real.log ((n : ℝ) + 1) + normSq t := by linarith
    calc ‖∏ k ∈ Finset.range n, (t + ((k : ℂ) + 1)) / ((k : ℂ) + 1)‖
        = Real.exp (Real.log ‖∏ k ∈ Finset.range n, (t + ((k : ℂ) + 1)) / ((k : ℂ) + 1)‖) :=
          (Real.exp_log hwpos).symm
      _ ≤ Real.exp (t.re * Real.log ((n : ℝ) + 1) + normSq t) := Real.exp_le_exp.mpr hfinal
      _ = Real.exp (normSq t) * ((n : ℝ) + 1) ^ t.re := by
          rw [Real.rpow_def_of_pos hbase, ← Real.exp_add]
          congr 1
          ring

/-! ### Summability of the pole series -/

/-- Absolute convergence of the pole series with a real denominator, the form to which both
the complex pole series and the term-by-term integration reduce: for `t.re < 0` and `σ < 0`,
`∑ ‖Ring.choose (t + n) n‖ / (n - σ)` converges. The restriction `t.re < 0` is sharp: at
`t = 0` every numerator equals `1` and the series is the harmonic series. -/
theorem summable_norm_ringChoose_div {t : ℂ} (ht : t.re < 0) {σ : ℝ} (hσ : σ < 0) :
    Summable fun n : ℕ => ‖Ring.choose (t + (n : ℂ)) n‖ / ((n : ℝ) - σ) := by
  set d : ℝ := min (-σ) 1 with hd_def
  have hd : 0 < d := lt_min (by linarith) one_pos
  have hd1 : d ≤ 1 := min_le_right _ _
  have hds : d ≤ -σ := min_le_left _ _
  have hcomp : Summable fun n : ℕ =>
      Real.exp (normSq t) / d * ((n : ℝ) + 1) ^ (t.re - 1) := by
    refine Summable.mul_left _ ?_
    have h1 : Summable fun n : ℕ => ((n : ℝ)) ^ (t.re - 1) :=
      Real.summable_nat_rpow.mpr (by linarith)
    refine ((summable_nat_add_iff 1).mpr h1).congr fun n => ?_
    rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 from by push_cast; ring]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hcomp
  · have hpos : (0 : ℝ) < (n : ℝ) - σ := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    positivity
  · have hbase : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hden : d * ((n : ℝ) + 1) ≤ (n : ℝ) - σ := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hd1) hnn]
    have hdenpos : (0 : ℝ) < d * ((n : ℝ) + 1) := by positivity
    have hnum : ‖Ring.choose (t + (n : ℂ)) n‖ ≤ Real.exp (normSq t) * ((n : ℝ) + 1) ^ t.re :=
      norm_ringChoose_add_natCast_le ht.le n
    have hnumnn : (0 : ℝ) ≤ Real.exp (normSq t) * ((n : ℝ) + 1) ^ t.re := by positivity
    have hsplit : ((n : ℝ) + 1) ^ (t.re - 1) = ((n : ℝ) + 1) ^ t.re / ((n : ℝ) + 1) := by
      rw [Real.rpow_sub hbase, Real.rpow_one]
    have hrhs : Real.exp (normSq t) / d * (((n : ℝ) + 1) ^ t.re / ((n : ℝ) + 1))
        = (Real.exp (normSq t) * ((n : ℝ) + 1) ^ t.re) / (d * ((n : ℝ) + 1)) := by
      field_simp
    rw [hsplit, hrhs]
    exact div_le_div₀ hnumnn hnum hdenpos hden

/-! ### The binomial series with `Ring.choose (t + n) n` coefficients -/

/-- Mathlib's binomial series `one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero`, as a
`HasSum` on the open unit disc with the coefficients written as `Ring.choose (t + n) n`:
`(1 - x) ^ (-t - 1) = ∑' n, Ring.choose (t + n) n * x ^ n`. -/
theorem hasSum_ringChoose_mul_pow (t : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => Ring.choose (t + (n : ℂ)) n * x ^ n) ((1 - x) ^ (-t - 1)) := by
  have hball : x ∈ Metric.eball (0 : ℂ) 1 := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 from by simp, Metric.eball_ofReal]
    simpa using hx
  have h := (Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (t + 1)).hasSum hball
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at h
  have hcoef : (fun n : ℕ => Ring.choose (t + 1 + (n : ℂ) - 1) n * x ^ n)
      = fun n : ℕ => Ring.choose (t + (n : ℂ)) n * x ^ n := by
    funext n
    rw [show t + 1 + (n : ℂ) - 1 = t + (n : ℂ) from by ring]
  have hval : (1 : ℂ) / (1 - x) ^ (t + 1) = (1 - x) ^ (-t - 1) := by
    rw [show (-t - 1 : ℂ) = -(t + 1) from by ring, Complex.cpow_neg, one_div]
  rw [hcoef, hval] at h
  exact h

/-! ### The Mittag-Leffler expansion -/

/-- Auxiliary normalized form of `Complex.hasSum_betaIntegral`, with the pole variable `s`
in the left half-plane so that the poles sit at `s = 0, 1, 2, …`. -/
private theorem hasSum_betaIntegral_aux {s t : ℂ} (hs : s.re < 0) (ht : t.re < 0) :
    HasSum (fun n : ℕ => Ring.choose (t + (n : ℂ)) n / ((n : ℂ) - s))
      (betaIntegral (-s) (-t)) := by
  classical
  set F : ℕ → ℝ → ℂ := fun n x =>
    Ring.choose (t + (n : ℂ)) n * (x : ℂ) ^ ((n : ℂ) - s - 1) with hF_def
  have hexp : ∀ n : ℕ, (-1 : ℝ) < ((n : ℂ) - s - 1).re := by
    intro n
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [Complex.sub_re, Complex.natCast_re, Complex.one_re]
    linarith
  have hexpre : ∀ n : ℕ, ((n : ℂ) - s - 1).re = (n : ℝ) - s.re - 1 := by
    intro n; simp
  have hcpowint : ∀ n : ℕ,
      MeasureTheory.IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((n : ℂ) - s - 1))
        (Set.Ioo 0 1) MeasureTheory.volume := by
    intro n
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
    exact intervalIntegral.intervalIntegrable_cpow' (hexp n)
  have hFint : ∀ n : ℕ, MeasureTheory.Integrable (F n)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    intro n
    exact (hcpowint n).const_mul _
  have hterm : ∀ n : ℕ,
      ∫ x in Set.Ioo (0 : ℝ) 1, F n x = Ring.choose (t + (n : ℂ)) n / ((n : ℂ) - s) := by
    intro n
    simp only [hF_def]
    rw [MeasureTheory.integral_const_mul, integral_Ioo_cpow (hexp n)]
    rw [show (n : ℂ) - s - 1 + 1 = (n : ℂ) - s from by ring]
    ring
  have hnormeq : ∀ n : ℕ, ∫ x in Set.Ioo (0 : ℝ) 1, ‖F n x‖
      = ‖Ring.choose (t + (n : ℂ)) n‖ / ((n : ℝ) - s.re) := by
    intro n
    have hrpos : (-1 : ℝ) < (n : ℝ) - s.re - 1 := by
      have := hexp n
      rw [hexpre n] at this
      exact this
    have hcongr : Set.EqOn (fun x : ℝ => ‖F n x‖)
        (fun x : ℝ => ‖Ring.choose (t + (n : ℂ)) n‖ * x ^ ((n : ℝ) - s.re - 1))
        (Set.Ioo 0 1) := by
      intro x hx
      simp only [hF_def, norm_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx.1, hexpre n]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hcongr,
      MeasureTheory.integral_const_mul, integral_Ioo_rpow hrpos]
    rw [show (n : ℝ) - s.re - 1 + 1 = (n : ℝ) - s.re from by ring]
    ring
  have hFsum : Summable fun n : ℕ => ∫ x in Set.Ioo (0 : ℝ) 1, ‖F n x‖ := by
    refine (summable_norm_ringChoose_div ht hs).congr fun n => ?_
    rw [hnormeq n]
  have hmain := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1)) hFint hFsum
  have hpt : Set.EqOn (fun x : ℝ => ∑' n : ℕ, F n x)
      (fun x : ℝ => (x : ℂ) ^ (-s - 1) * (1 - (x : ℂ)) ^ (-t - 1)) (Set.Ioo 0 1) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hxc : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx0
    have hxnorm : ‖(x : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact hx.2
    have h := (hasSum_ringChoose_mul_pow t hxnorm).mul_left ((x : ℂ) ^ (-s - 1))
    have hfe : (fun n : ℕ => (x : ℂ) ^ (-s - 1) * (Ring.choose (t + (n : ℂ)) n * (x : ℂ) ^ n))
        = fun n : ℕ => F n x := by
      funext n
      simp only [hF_def]
      rw [show (n : ℂ) - s - 1 = -s - 1 + (n : ℂ) from by ring, Complex.cpow_add _ _ hxc,
        Complex.cpow_natCast]
      ring
    rw [hfe] at h
    exact h.tsum_eq
  have hIntegral :
      ∫ x in Set.Ioo (0 : ℝ) 1, (∑' n : ℕ, F n x) = betaIntegral (-s) (-t) := by
    rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo hpt
  rw [hIntegral] at hmain
  refine hmain.congr_fun fun n => ?_
  exact (hterm n).symm

/-- **The Mittag-Leffler (partial-fraction) expansion of the Beta function.**

For `0 < re u` and `0 < re v`,

`Β(u, v) = ∑' n : ℕ, Ring.choose (n - v) n / (n + u)`,

an absolutely convergent sum over the simple poles of `u ↦ Β(u, v)` at `u = 0, -1, -2, …`,
the pole at `u = -n` having residue `Ring.choose (n - v) n = (1 - v)⁽ⁿ⁾ / n!`. The proof
expands `(1 - x) ^ (v - 1)` in the Euler integral by the binomial series and integrates term
by term; absolute convergence is `Complex.summable_norm_ringChoose_div`. -/
theorem hasSum_betaIntegral {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    HasSum (fun n : ℕ => Ring.choose ((n : ℂ) - v) n / ((n : ℂ) + u)) (betaIntegral u v) := by
  have hs : (-u).re < 0 := by rw [Complex.neg_re]; linarith
  have ht : (-v).re < 0 := by rw [Complex.neg_re]; linarith
  have h := hasSum_betaIntegral_aux hs ht
  simpa [neg_neg, sub_neg_eq_add, neg_add_eq_sub] using h

end Complex
