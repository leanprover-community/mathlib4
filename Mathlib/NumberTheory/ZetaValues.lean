/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries

#align_import number_theory.zeta_values from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Critical values of the Riemann zeta function

In this file we prove formulae for the critical values of `ζ(s)`, and more generally of Hurwitz
zeta functions, in terms of Bernoulli polynomials.

## Main results:

* `hasSum_zeta_nat`: the final formula for zeta values,
  $$\zeta(2k) = \frac{(-1)^{(k + 1)} 2 ^ {2k - 1} \pi^{2k} B_{2 k}}{(2 k)!}.$$
* `hasSum_zeta_two` and `hasSum_zeta_four`: special cases given explicitly.
* `hasSum_one_div_nat_pow_mul_cos`: a formula for the sum `∑ (n : ℕ), cos (2 π i n x) / n ^ k` as
  an explicit multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 2` even.
* `hasSum_one_div_nat_pow_mul_sin`: a formula for the sum `∑ (n : ℕ), sin (2 π i n x) / n ^ k` as
  an explicit multiple of `Bₖ(x)`, for any `x ∈ [0, 1]` and `k ≥ 3` odd.
-/

noncomputable section

open scoped Nat Real Interval

open Complex MeasureTheory Set intervalIntegral

local notation "𝕌" => UnitAddCircle

attribute [local instance] Real.fact_zero_lt_one

section BernoulliFunProps

/-! Simple properties of the Bernoulli polynomial, as a function `ℝ → ℝ`. -/


/-- The function `x ↦ Bₖ(x) : ℝ → ℝ`. -/
def bernoulliFun (k : ℕ) (x : ℝ) : ℝ :=
  (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli k)).eval x
#align bernoulli_fun bernoulliFun

theorem bernoulliFun_eval_zero (k : ℕ) : bernoulliFun k 0 = bernoulli' k := by
  rw [bernoulliFun, Polynomial.eval_zero_map, Polynomial.bernoulli_eval_zero, eq_ratCast]
#align bernoulli_fun_eval_zero bernoulliFun_eval_zero

theorem bernoulliFun_endpoints_eq_of_ne_one {k : ℕ} (hk : k ≠ 1) :
    bernoulliFun k 1 = bernoulliFun k 0 := by
  rw [bernoulliFun_eval_zero, bernoulliFun, Polynomial.eval_one_map, Polynomial.bernoulli_eval_one,
    bernoulli'_eq_bernoulli_of_ne_one hk, eq_ratCast]
#align bernoulli_fun_endpoints_eq_of_ne_one bernoulliFun_endpoints_eq_of_ne_one

theorem bernoulliFun_eval_one (k : ℕ) : bernoulliFun k 1 = bernoulliFun k 0 + ite (k = 1) 1 0 := by
  rw [bernoulliFun, bernoulliFun_eval_zero, Polynomial.eval_one_map, Polynomial.bernoulli_eval_one]
  split_ifs with h
  · rw [h, bernoulli_one, bernoulli'_one, eq_ratCast]
    push_cast; ring
  · rw [bernoulli'_eq_bernoulli_of_ne_one h, add_zero, eq_ratCast]
#align bernoulli_fun_eval_one bernoulliFun_eval_one

theorem hasDerivAt_bernoulliFun (k : ℕ) (x : ℝ) :
    HasDerivAt (bernoulliFun k) (k * bernoulliFun (k - 1) x) x := by
  convert ((Polynomial.bernoulli k).map <| algebraMap ℚ ℝ).hasDerivAt x using 1
  simp only [bernoulliFun, Polynomial.derivative_map, Polynomial.derivative_bernoulli k,
    Polynomial.map_mul, Polynomial.map_nat_cast, Polynomial.eval_mul, Polynomial.eval_nat_cast]
#align has_deriv_at_bernoulli_fun hasDerivAt_bernoulliFun

theorem antideriv_bernoulliFun (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => bernoulliFun (k + 1) x / (k + 1)) (bernoulliFun k x) x := by
  convert (hasDerivAt_bernoulliFun (k + 1) x).div_const _ using 1
  field_simp [Nat.cast_add_one_ne_zero k]
  ring
#align antideriv_bernoulli_fun antideriv_bernoulliFun

theorem integral_bernoulliFun_eq_zero {k : ℕ} (hk : k ≠ 0) :
    ∫ x : ℝ in (0)..1, bernoulliFun k x = 0 := by
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => antideriv_bernoulliFun k x)
      ((Polynomial.continuous _).intervalIntegrable _ _)]
  rw [bernoulliFun_eval_one]
  split_ifs with h
  · exfalso; exact hk (Nat.succ_inj'.mp h)
  · simp
#align integral_bernoulli_fun_eq_zero integral_bernoulliFun_eq_zero

end BernoulliFunProps

section BernoulliFourierCoeffs

/-! Compute the Fourier coefficients of the Bernoulli functions via integration by parts. -/


/-- The `n`-th Fourier coefficient of the `k`-th Bernoulli function on the interval `[0, 1]`. -/
def bernoulliFourierCoeff (k : ℕ) (n : ℤ) : ℂ :=
  fourierCoeffOn zero_lt_one (fun x => bernoulliFun k x) n
#align bernoulli_fourier_coeff bernoulliFourierCoeff

/-- Recurrence relation (in `k`) for the `n`-th Fourier coefficient of `Bₖ`. -/
theorem bernoulliFourierCoeff_recurrence (k : ℕ) {n : ℤ} (hn : n ≠ 0) :
    bernoulliFourierCoeff k n =
      1 / (-2 * π * I * n) * (ite (k = 1) 1 0 - k * bernoulliFourierCoeff (k - 1) n) := by
  unfold bernoulliFourierCoeff
  rw [fourierCoeffOn_of_hasDerivAt zero_lt_one hn
      (fun x _ => (hasDerivAt_bernoulliFun k x).ofReal_comp)
      ((continuous_ofReal.comp <|
            continuous_const.mul <| Polynomial.continuous _).intervalIntegrable
        _ _)]
  simp_rw [ofReal_one, ofReal_zero, sub_zero, one_mul]
  rw [QuotientAddGroup.mk_zero, fourier_eval_zero, one_mul, ← ofReal_sub, bernoulliFun_eval_one,
    add_sub_cancel']
  congr 2
  · split_ifs <;> simp only [ofReal_one, ofReal_zero, one_mul]
  · simp_rw [ofReal_mul, ofReal_nat_cast, fourierCoeffOn.const_mul]
#align bernoulli_fourier_coeff_recurrence bernoulliFourierCoeff_recurrence

/-- The Fourier coefficients of `B₀(x) = 1`. -/
theorem bernoulli_zero_fourier_coeff {n : ℤ} (hn : n ≠ 0) : bernoulliFourierCoeff 0 n = 0 := by
  simpa using bernoulliFourierCoeff_recurrence 0 hn
#align bernoulli_zero_fourier_coeff bernoulli_zero_fourier_coeff

/-- The `0`-th Fourier coefficient of `Bₖ(x)`. -/
theorem bernoulliFourierCoeff_zero {k : ℕ} (hk : k ≠ 0) : bernoulliFourierCoeff k 0 = 0 := by
  simp_rw [bernoulliFourierCoeff, fourierCoeffOn_eq_integral, neg_zero, fourier_zero, sub_zero,
    div_one, one_smul, intervalIntegral.integral_ofReal, integral_bernoulliFun_eq_zero hk,
    ofReal_zero]
#align bernoulli_fourier_coeff_zero bernoulliFourierCoeff_zero

theorem bernoulliFourierCoeff_eq {k : ℕ} (hk : k ≠ 0) (n : ℤ) :
    bernoulliFourierCoeff k n = -k ! / (2 * π * I * n) ^ k := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · rw [bernoulliFourierCoeff_zero hk, Int.cast_zero, mul_zero, zero_pow hk,
      div_zero]
  refine' Nat.le_induction _ (fun k hk h'k => _) k (Nat.one_le_iff_ne_zero.mpr hk)
  · rw [bernoulliFourierCoeff_recurrence 1 hn]
    simp only [Nat.cast_one, tsub_self, neg_mul, one_mul, eq_self_iff_true, if_true,
      Nat.factorial_one, pow_one, inv_I, mul_neg]
    rw [bernoulli_zero_fourier_coeff hn, sub_zero, mul_one, div_neg, neg_div]
  · rw [bernoulliFourierCoeff_recurrence (k + 1) hn, Nat.add_sub_cancel k 1]
    split_ifs with h
    · exfalso; exact (ne_of_gt (Nat.lt_succ_iff.mpr hk)) h
    · rw [h'k, Nat.factorial_succ, zero_sub, Nat.cast_mul, pow_add, pow_one, neg_div, mul_neg,
        mul_neg, mul_neg, neg_neg, neg_mul, neg_mul, neg_mul, div_neg]
      field_simp [Int.cast_ne_zero.mpr hn, I_ne_zero]
      ring_nf
#align bernoulli_fourier_coeff_eq bernoulliFourierCoeff_eq

end BernoulliFourierCoeffs

section BernoulliPeriodized

/-! In this section we use the above evaluations of the Fourier coefficients of Bernoulli
polynomials, together with the theorem `has_pointwise_sum_fourier_series_of_summable` from Fourier
theory, to obtain an explicit formula for `∑ (n:ℤ), 1 / n ^ k * fourier n x`. -/


/-- The Bernoulli polynomial, extended from `[0, 1)` to the unit circle. -/
def periodizedBernoulli (k : ℕ) : 𝕌 → ℝ :=
  AddCircle.liftIco 1 0 (bernoulliFun k)
#align periodized_bernoulli periodizedBernoulli

theorem periodizedBernoulli.continuous {k : ℕ} (hk : k ≠ 1) : Continuous (periodizedBernoulli k) :=
  AddCircle.liftIco_zero_continuous
    (mod_cast (bernoulliFun_endpoints_eq_of_ne_one hk).symm)
    (Polynomial.continuous _).continuousOn
#align periodized_bernoulli.continuous periodizedBernoulli.continuous

theorem fourierCoeff_bernoulli_eq {k : ℕ} (hk : k ≠ 0) (n : ℤ) :
    fourierCoeff ((↑) ∘ periodizedBernoulli k : 𝕌 → ℂ) n = -k ! / (2 * π * I * n) ^ k := by
  have : ((↑) ∘ periodizedBernoulli k : 𝕌 → ℂ) = AddCircle.liftIco 1 0 ((↑) ∘ bernoulliFun k) := by
    ext1 x; rfl
  rw [this, fourierCoeff_liftIco_eq]
  simpa only [zero_add] using bernoulliFourierCoeff_eq hk n
#align fourier_coeff_bernoulli_eq fourierCoeff_bernoulli_eq

theorem summable_bernoulli_fourier {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun n => -k ! / (2 * π * I * n) ^ k : ℤ → ℂ) := by
  have :
      ∀ n : ℤ, -(k ! : ℂ) / (2 * π * I * n) ^ k = -k ! / (2 * π * I) ^ k * (1 / (n : ℂ) ^ k) := by
    intro n; rw [mul_one_div, div_div, ← mul_pow]
  simp_rw [this]
  refine Summable.mul_left _ <| .of_norm ?_
  have : (fun x : ℤ => ‖1 / (x : ℂ) ^ k‖) = fun x : ℤ => |1 / (x : ℝ) ^ k| := by
    ext1 x
    rw [norm_eq_abs, ← Complex.abs_ofReal]
    congr 1
    norm_cast
  simp_rw [this]
  rwa [summable_abs_iff, Real.summable_one_div_int_pow]
#align summable_bernoulli_fourier summable_bernoulli_fourier

theorem hasSum_one_div_pow_mul_fourier_mul_bernoulliFun {k : ℕ} (hk : 2 ≤ k) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℤ => 1 / (n : ℂ) ^ k * fourier n (x : 𝕌))
      (-(2 * π * I) ^ k / k ! * bernoulliFun k x) := by
  -- first show it suffices to prove result for `Ico 0 1`
  suffices ∀ {y : ℝ}, y ∈ Ico (0 : ℝ) 1 →
      HasSum (λ (n : ℤ) => 1 / (n : ℂ) ^ k * fourier n y)
        (-(2 * (π : ℂ) * I) ^ k / k ! * bernoulliFun k y) by
    rw [← Ico_insert_right (zero_le_one' ℝ), mem_insert_iff, or_comm] at hx
    rcases hx with (hx | rfl)
    · exact this hx
    · convert this (left_mem_Ico.mpr zero_lt_one) using 1
      · rw [AddCircle.coe_period, QuotientAddGroup.mk_zero]
      · rw [bernoulliFun_endpoints_eq_of_ne_one (by omega : k ≠ 1)]
  intro y hy
  let B : C(𝕌, ℂ) :=
    ContinuousMap.mk ((↑) ∘ periodizedBernoulli k)
      (continuous_ofReal.comp (periodizedBernoulli.continuous (by omega)))
  have step1 : ∀ n : ℤ, fourierCoeff B n = -k ! / (2 * π * I * n) ^ k := by
    rw [ContinuousMap.coe_mk]; exact fourierCoeff_bernoulli_eq (by omega : k ≠ 0)
  have step2 :=
    has_pointwise_sum_fourier_series_of_summable
      ((summable_bernoulli_fourier hk).congr fun n => (step1 n).symm) y
  simp_rw [step1] at step2
  convert step2.mul_left (-(2 * ↑π * I) ^ k / (k ! : ℂ)) using 2 with n
  rw [smul_eq_mul, ← mul_assoc, mul_div, mul_neg, div_mul_cancel, neg_neg, mul_pow _ (n : ℂ),
    ← div_div, div_self]
  · rw [Ne.def, pow_eq_zero_iff', not_and_or]
    exact Or.inl two_pi_I_ne_zero
  · exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  · rw [ContinuousMap.coe_mk, Function.comp_apply, ofReal_inj, periodizedBernoulli,
      AddCircle.liftIco_coe_apply (by rwa [zero_add])]
#align has_sum_one_div_pow_mul_fourier_mul_bernoulli_fun hasSum_one_div_pow_mul_fourier_mul_bernoulliFun

end BernoulliPeriodized

section Cleanup

-- This section is just reformulating the results in a nicer form.
theorem hasSum_one_div_nat_pow_mul_fourier {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum
      (fun n : ℕ =>
        (1 : ℂ) / (n : ℂ) ^ k * (fourier n (x : 𝕌) + (-1 : ℂ) ^ k * fourier (-n) (x : 𝕌)))
      (-(2 * π * I) ^ k / k ! * bernoulliFun k x) := by
  convert (hasSum_one_div_pow_mul_fourier_mul_bernoulliFun hk hx).sum_nat_of_sum_int using 1
  · ext1 n
    rw [Int.cast_neg, mul_add, ← mul_assoc]
    conv_rhs => rw [neg_eq_neg_one_mul, mul_pow, ← div_div]
    congr 2
    rw [div_mul_eq_mul_div₀, one_mul]
    congr 1
    rw [eq_div_iff, ← mul_pow, ← neg_eq_neg_one_mul, neg_neg, one_pow]
    apply pow_ne_zero; rw [neg_ne_zero]; exact one_ne_zero
  · rw [Int.cast_zero, zero_pow (by positivity : k ≠ 0), div_zero, zero_mul, add_zero]
#align has_sum_one_div_nat_pow_mul_fourier hasSum_one_div_nat_pow_mul_fourier

theorem hasSum_one_div_nat_pow_mul_cos {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k) * Real.cos (2 * π * n * x))
      ((-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
        (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k))).eval x) := by
  have :
    HasSum (fun n : ℕ => 1 / (n : ℂ) ^ (2 * k) * (fourier n (x : 𝕌) + fourier (-n) (x : 𝕌)))
      ((-1 : ℂ) ^ (k + 1) * (2 * (π : ℂ)) ^ (2 * k) / (2 * k)! * bernoulliFun (2 * k) x) := by
    convert
      hasSum_one_div_nat_pow_mul_fourier (by omega : 2 ≤ 2 * k)
        hx using 3
    · rw [pow_mul (-1 : ℂ), neg_one_sq, one_pow, one_mul]
    · rw [pow_add, pow_one]
      conv_rhs =>
        rw [mul_pow]
        congr
        congr
        · skip
        · rw [pow_mul, I_sq]
      ring
  have ofReal_two : ((2 : ℝ) : ℂ) = 2 := by norm_cast
  convert ((hasSum_iff _ _).mp (this.div_const 2)).1 with n
  · convert (ofReal_re _).symm
    rw [ofReal_mul]; rw [← mul_div]; congr
    · rw [ofReal_div, ofReal_one, ofReal_pow]; rfl
    · rw [ofReal_cos, ofReal_mul, fourier_coe_apply, fourier_coe_apply, cos, ofReal_one, div_one,
        div_one, ofReal_mul, ofReal_mul, ofReal_two, Int.cast_neg, Int.cast_ofNat,
        ofReal_nat_cast]
      congr 3
      · ring
      · ring
  · convert (ofReal_re _).symm
    rw [ofReal_mul, ofReal_div, ofReal_div, ofReal_mul, ofReal_pow, ofReal_pow, ofReal_neg,
      ofReal_nat_cast, ofReal_mul, ofReal_two, ofReal_one]
    rw [bernoulliFun]
    ring
#align has_sum_one_div_nat_pow_mul_cos hasSum_one_div_nat_pow_mul_cos

theorem hasSum_one_div_nat_pow_mul_sin {k : ℕ} (hk : k ≠ 0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k + 1) * Real.sin (2 * π * n * x))
      ((-1 : ℝ) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / (2 * k + 1)! *
        (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * k + 1))).eval x) := by
  have :
    HasSum (fun n : ℕ => 1 / (n : ℂ) ^ (2 * k + 1) * (fourier n (x : 𝕌) - fourier (-n) (x : 𝕌)))
      ((-1 : ℂ) ^ (k + 1) * I * (2 * π : ℂ) ^ (2 * k + 1) / (2 * k + 1)! *
        bernoulliFun (2 * k + 1) x) := by
    convert
      hasSum_one_div_nat_pow_mul_fourier
        (by omega : 2 ≤ 2 * k + 1) hx using 1
    · ext1 n
      rw [pow_add (-1 : ℂ), pow_mul (-1 : ℂ), neg_one_sq, one_pow, one_mul, pow_one, ←
        neg_eq_neg_one_mul, ← sub_eq_add_neg]
    · congr
      rw [pow_add, pow_one]
      conv_rhs =>
        rw [mul_pow]
        congr
        congr
        · skip
        · rw [pow_add, pow_one, pow_mul, I_sq]
      ring
  have ofReal_two : ((2 : ℝ) : ℂ) = 2 := by norm_cast
  convert ((hasSum_iff _ _).mp (this.div_const (2 * I))).1
  · convert (ofReal_re _).symm
    rw [ofReal_mul]; rw [← mul_div]; congr
    · rw [ofReal_div, ofReal_one, ofReal_pow]; rfl
    · rw [ofReal_sin, ofReal_mul, fourier_coe_apply, fourier_coe_apply, sin, ofReal_one, div_one,
        div_one, ofReal_mul, ofReal_mul, ofReal_two, Int.cast_neg, Int.cast_ofNat,
        ofReal_nat_cast, ← div_div, div_I, div_mul_eq_mul_div₀, ← neg_div, ← neg_mul, neg_sub]
      congr 4
      · ring
      · ring
  · convert (ofReal_re _).symm
    rw [ofReal_mul, ofReal_div, ofReal_div, ofReal_mul, ofReal_pow, ofReal_pow, ofReal_neg,
      ofReal_nat_cast, ofReal_mul, ofReal_two, ofReal_one, ← div_div, div_I,
      div_mul_eq_mul_div₀]
    have : ∀ α β γ δ : ℂ, α * I * β / γ * δ * I = I ^ 2 * α * β / γ * δ := by intros; ring
    rw [this, I_sq]
    rw [bernoulliFun]
    ring
#align has_sum_one_div_nat_pow_mul_sin hasSum_one_div_nat_pow_mul_sin

theorem hasSum_zeta_nat {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k))
      ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
        bernoulli (2 * k) / (2 * k)!) := by
  rw [← bernoulli'_eq_bernoulli_of_ne_one (by simp)]
  convert hasSum_one_div_nat_pow_mul_cos hk (left_mem_Icc.mpr zero_le_one) using 1
  · ext1 n; rw [mul_zero, Real.cos_zero, mul_one]
  rw [Polynomial.eval_zero_map, Polynomial.bernoulli_eval_zero, eq_ratCast]
  have : (2 : ℝ) ^ (2 * k - 1) = (2 : ℝ) ^ (2 * k) / 2 := by
    rw [eq_div_iff (two_ne_zero' ℝ)]
    conv_lhs =>
      congr
      · skip
      · rw [← pow_one (2 : ℝ)]
    rw [← pow_add, Nat.sub_add_cancel]
    omega
  rw [this, mul_pow]
  ring
#align has_sum_zeta_nat hasSum_zeta_nat

end Cleanup

section Examples

theorem hasSum_zeta_two : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (π ^ 2 / 6) := by
  convert hasSum_zeta_nat one_ne_zero using 1
  rw [mul_one, bernoulli_two]
  norm_num [Nat.factorial]; field_simp; ring
#align has_sum_zeta_two hasSum_zeta_two

theorem hasSum_zeta_four : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) (π ^ 4 / 90) := by
  convert hasSum_zeta_nat two_ne_zero using 1
  norm_num [Nat.factorial]; field_simp; ring
#align has_sum_zeta_four hasSum_zeta_four

theorem Polynomial.bernoulli_three_eval_one_quarter :
    (Polynomial.bernoulli 3).eval (1 / 4) = 3 / 64 := by
  simp_rw [Polynomial.bernoulli, Finset.sum_range_succ, Polynomial.eval_add,
    Polynomial.eval_monomial]
  rw [Finset.sum_range_zero, Polynomial.eval_zero, zero_add, bernoulli'_zero, bernoulli'_one,
    bernoulli'_eq_bernoulli_of_ne_one (by decide : 2 ≠ 1), bernoulli_two,
    bernoulli'_eq_bernoulli_of_ne_one (by decide : 3 ≠ 1), bernoulli_three]
  norm_num
#align polynomial.bernoulli_three_eval_one_quarter Polynomial.bernoulli_three_eval_one_quarter

/-- Explicit formula for `L(χ, 3)`, where `χ` is the unique nontrivial Dirichlet character modulo 4.
-/
theorem hasSum_L_function_mod_four_eval_three :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3 * Real.sin (π * n / 2)) (π ^ 3 / 32) := by
  -- Porting note: times out with
  -- convert hasSum_one_div_nat_pow_mul_sin one_ne_zero (_ : 1 / 4 ∈ Icc (0 : ℝ) 1)
  apply (congr_arg₂ HasSum ?_ ?_).to_iff.mp <|
    hasSum_one_div_nat_pow_mul_sin one_ne_zero (?_ : 1 / 4 ∈ Icc (0 : ℝ) 1)
  · ext1 n
    norm_num
    left
    congr 1
    ring
  · have : (1 / 4 : ℝ) = (algebraMap ℚ ℝ) (1 / 4 : ℚ) := by norm_num
    rw [this, mul_pow, Polynomial.eval_map, Polynomial.eval₂_at_apply, (by decide : 2 * 1 + 1 = 3),
      Polynomial.bernoulli_three_eval_one_quarter]
    norm_num [Nat.factorial]; field_simp; ring
  · rw [mem_Icc]; constructor; linarith; linarith
set_option linter.uppercaseLean3 false in
#align has_sum_L_function_mod_four_eval_three hasSum_L_function_mod_four_eval_three

end Examples
