/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

#align_import analysis.special_functions.integrals from "leanprover-community/mathlib"@"011cafb4a5bc695875d186e245d6b3df03bf6c40"

/-!
# Integration of specific interval integrals

This file contains proofs of the integrals of various specific functions. This includes:
* Integrals of simple functions, such as `id`, `pow`, `inv`, `exp`, `log`
* Integrals of some trigonometric functions, such as `sin`, `cos`, `1 / (1 + x^2)`
* The integral of `cos x ^ 2 - sin x ^ 2`
* Reduction formulae for the integrals of `sin x ^ n` and `cos x ^ n` for `n ≥ 2`
* The computation of `∫ x in 0..π, sin x ^ n` as a product for even and odd `n` (used in proving the
  Wallis product for pi)
* Integrals of the form `sin x ^ m * cos x ^ n`

With these lemmas, many simple integrals can be computed by `simp` or `norm_num`.
See `test/integration.lean` for specific examples.

This file also contains some facts about the interval integrability of specific functions.

This file is still being developed.

## Tags

integrate, integration, integrable, integrability
-/


open Real Nat Set Finset

open scoped Real BigOperators Interval

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

variable {a b : ℝ} (n : ℕ)

namespace intervalIntegral

open MeasureTheory

variable {f : ℝ → ℝ} {μ ν : Measure ℝ} [IsLocallyFiniteMeasure μ] (c d : ℝ)

/-! ### Interval integrability -/


@[simp]
theorem intervalIntegrable_pow : IntervalIntegrable (fun x => x ^ n) μ a b :=
  (continuous_pow n).intervalIntegrable a b
#align interval_integral.interval_integrable_pow intervalIntegral.intervalIntegrable_pow

theorem intervalIntegrable_zpow {n : ℤ} (h : 0 ≤ n ∨ (0 : ℝ) ∉ [[a, b]]) :
    IntervalIntegrable (fun x => x ^ n) μ a b :=
  (continuousOn_id.zpow₀ n fun _ hx => h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable
#align interval_integral.interval_integrable_zpow intervalIntegral.intervalIntegrable_zpow

/-- See `intervalIntegrable_rpow'` for a version with a weaker hypothesis on `r`, but assuming the
measure is volume. -/
theorem intervalIntegrable_rpow {r : ℝ} (h : 0 ≤ r ∨ (0 : ℝ) ∉ [[a, b]]) :
    IntervalIntegrable (fun x => x ^ r) μ a b :=
  (continuousOn_id.rpow_const fun _ hx =>
    h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable
#align interval_integral.interval_integrable_rpow intervalIntegral.intervalIntegrable_rpow

/-- See `intervalIntegrable_rpow` for a version applying to any locally finite measure, but with a
stronger hypothesis on `r`. -/
theorem intervalIntegrable_rpow' {r : ℝ} (h : -1 < r) :
    IntervalIntegrable (fun x => x ^ r) volume a b := by
  suffices ∀ c : ℝ, IntervalIntegrable (fun x => x ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x => x ^ r) volume 0 c := by
    intro c hc
    rw [intervalIntegrable_iff, uIoc_of_le hc]
    have hderiv : ∀ x ∈ Ioo 0 c, HasDerivAt (fun x : ℝ => x ^ (r + 1) / (r + 1)) (x ^ r) x := by
      intro x hx
      convert (Real.hasDerivAt_rpow_const (p := r + 1) (Or.inl hx.1.ne')).div_const (r + 1) using 1
      field_simp [(by linarith : r + 1 ≠ 0)]; ring
    apply integrableOn_deriv_of_nonneg _ hderiv
    · intro x hx; apply rpow_nonneg_of_nonneg hx.1.le
    · refine' (continuousOn_id.rpow_const _).div_const _; intro x _; right; linarith
  intro c; rcases le_total 0 c with (hc | hc)
  -- ⊢ IntervalIntegrable (fun x => x ^ r) volume 0 c
           -- ⊢ IntervalIntegrable (fun x => x ^ r) volume 0 c
  · exact this c hc
    -- 🎉 no goals
  · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
    -- ⊢ IntervalIntegrable (fun x => (-x) ^ r) volume 0 (-c)
    have m := (this (-c) (by linarith)).smul (cos (r * π))
    -- ⊢ IntervalIntegrable (fun x => (-x) ^ r) volume 0 (-c)
    rw [intervalIntegrable_iff] at m ⊢
    -- ⊢ IntegrableOn (fun x => (-x) ^ r) (Ι 0 (-c))
    refine' m.congr_fun _ measurableSet_Ioc; intro x hx
    -- ⊢ EqOn (cos (r * π) • fun x => x ^ r) (fun x => (-x) ^ r) (Ι 0 (-c))
                                             -- ⊢ (cos (r * π) • fun x => x ^ r) x = (fun x => (-x) ^ r) x
    rw [uIoc_of_le (by linarith : 0 ≤ -c)] at hx
    -- ⊢ (cos (r * π) • fun x => x ^ r) x = (fun x => (-x) ^ r) x
    simp only [Pi.smul_apply, Algebra.id.smul_eq_mul, log_neg_eq_log, mul_comm,
      rpow_def_of_pos hx.1, rpow_def_of_neg (by linarith [hx.1] : -x < 0)]
#align interval_integral.interval_integrable_rpow' intervalIntegral.intervalIntegrable_rpow'

/-- See `intervalIntegrable_cpow'` for a version with a weaker hypothesis on `r`, but assuming the
measure is volume. -/
theorem intervalIntegrable_cpow {r : ℂ} (h : 0 ≤ r.re ∨ (0 : ℝ) ∉ [[a, b]]) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) μ a b := by
  by_cases h2 : (0 : ℝ) ∉ [[a, b]]
  -- ⊢ IntervalIntegrable (fun x => ↑x ^ r) μ a b
  · -- Easy case #1: 0 ∉ [a, b] -- use continuity.
    refine' (ContinuousAt.continuousOn fun x hx => _).intervalIntegrable
    -- ⊢ ContinuousAt (fun x => ↑x ^ r) x
    exact Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr <| ne_of_mem_of_not_mem hx h2)
    -- 🎉 no goals
  rw [eq_false h2, or_false_iff] at h
  -- ⊢ IntervalIntegrable (fun x => ↑x ^ r) μ a b
  rcases lt_or_eq_of_le h with (h' | h')
  -- ⊢ IntervalIntegrable (fun x => ↑x ^ r) μ a b
  · -- Easy case #2: 0 < re r -- again use continuity
    exact (Complex.continuous_ofReal_cpow_const h').intervalIntegrable _ _
    -- 🎉 no goals
  -- Now the hard case: re r = 0 and 0 is in the interval.
  refine' (IntervalIntegrable.intervalIntegrable_norm_iff _).mp _
  -- ⊢ AEStronglyMeasurable (fun x => ↑x ^ r) (Measure.restrict μ (Ι a b))
  · refine' (measurable_of_continuousOn_compl_singleton (0 : ℝ) _).aestronglyMeasurable
    -- ⊢ ContinuousOn (fun x => ↑x ^ r) {0}ᶜ
    exact ContinuousAt.continuousOn fun x hx =>
      Complex.continuousAt_ofReal_cpow_const x r (Or.inr hx)
  -- reduce to case of integral over `[0, c]`
  suffices : ∀ c : ℝ, IntervalIntegrable (fun x : ℝ => ‖(x:ℂ) ^ r‖) μ 0 c
  -- ⊢ IntervalIntegrable (fun t => ‖↑t ^ r‖) μ a b
  exact (this a).symm.trans (this b)
  -- ⊢ ∀ (c : ℝ), IntervalIntegrable (fun x => ‖↑x ^ r‖) μ 0 c
  intro c
  -- ⊢ IntervalIntegrable (fun x => ‖↑x ^ r‖) μ 0 c
  rcases le_or_lt 0 c with (hc | hc)
  -- ⊢ IntervalIntegrable (fun x => ‖↑x ^ r‖) μ 0 c
  · -- case `0 ≤ c`: integrand is identically 1
    have : IntervalIntegrable (fun _ => 1 : ℝ → ℝ) μ 0 c := intervalIntegrable_const
    -- ⊢ IntervalIntegrable (fun x => ‖↑x ^ r‖) μ 0 c
    rw [intervalIntegrable_iff_integrable_Ioc_of_le hc] at this ⊢
    -- ⊢ IntegrableOn (fun x => ‖↑x ^ r‖) (Set.Ioc 0 c)
    refine' IntegrableOn.congr_fun this (fun x hx => _) measurableSet_Ioc
    -- ⊢ 1 = ‖↑x ^ r‖
    dsimp only
    -- ⊢ 1 = ‖↑x ^ r‖
    rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hx.1, ← h', rpow_zero]
    -- 🎉 no goals
  · -- case `c < 0`: integrand is identically constant, *except* at `x = 0` if `r ≠ 0`.
    apply IntervalIntegrable.symm
    -- ⊢ IntervalIntegrable (fun x => ‖↑x ^ r‖) μ c 0
    rw [intervalIntegrable_iff_integrable_Ioc_of_le hc.le]
    -- ⊢ IntegrableOn (fun x => ‖↑x ^ r‖) (Set.Ioc c 0)
    have : Ioc c 0 = Ioo c 0 ∪ {(0 : ℝ)} := by
      rw [← Ioo_union_Icc_eq_Ioc hc (le_refl 0), ← Icc_def]
      simp_rw [← le_antisymm_iff, setOf_eq_eq_singleton']
    rw [this, integrableOn_union, and_comm]; constructor
    -- ⊢ IntegrableOn (fun x => ‖↑x ^ r‖) {0} ∧ IntegrableOn (fun x => ‖↑x ^ r‖) (Set …
                                             -- ⊢ IntegrableOn (fun x => ‖↑x ^ r‖) {0}
    · refine' integrableOn_singleton_iff.mpr (Or.inr _)
      -- ⊢ ↑↑μ {0} < ⊤
      exact isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure.lt_top_of_isCompact
        isCompact_singleton
    · have : ∀ x : ℝ, x ∈ Ioo c 0 → ‖Complex.exp (↑π * Complex.I * r)‖ = ‖(x : ℂ) ^ r‖ := by
        intro x hx
        rw [Complex.ofReal_cpow_of_nonpos hx.2.le, norm_mul, ← Complex.ofReal_neg,
          Complex.norm_eq_abs (_ ^ _), Complex.abs_cpow_eq_rpow_re_of_pos (neg_pos.mpr hx.2), ← h',
          rpow_zero, one_mul]
      refine' IntegrableOn.congr_fun _ this measurableSet_Ioo
      -- ⊢ IntegrableOn (fun x => ‖Complex.exp (↑π * Complex.I * r)‖) (Set.Ioo c 0)
      rw [integrableOn_const]
      -- ⊢ ‖Complex.exp (↑π * Complex.I * r)‖ = 0 ∨ ↑↑μ (Set.Ioo c 0) < ⊤
      refine' Or.inr ((measure_mono Set.Ioo_subset_Icc_self).trans_lt _)
      -- ⊢ ↑↑μ (Set.Icc c 0) < ⊤
      exact isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure.lt_top_of_isCompact isCompact_Icc
      -- 🎉 no goals
#align interval_integral.interval_integrable_cpow intervalIntegral.intervalIntegrable_cpow

/-- See `intervalIntegrable_cpow` for a version applying to any locally finite measure, but with a
stronger hypothesis on `r`. -/
theorem intervalIntegrable_cpow' {r : ℂ} (h : -1 < r.re) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) volume a b := by
  suffices ∀ c : ℝ, IntervalIntegrable (fun x => (x : ℂ) ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x => (x : ℂ) ^ r) volume 0 c := by
    intro c hc
    rw [← IntervalIntegrable.intervalIntegrable_norm_iff]
    · rw [intervalIntegrable_iff]
      apply IntegrableOn.congr_fun
      · rw [← intervalIntegrable_iff]; exact intervalIntegral.intervalIntegrable_rpow' h
      · intro x hx
        rw [uIoc_of_le hc] at hx
        dsimp only
        rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hx.1]
      · exact measurableSet_uIoc
    · refine' ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
      refine' ContinuousAt.continuousOn fun x hx => _
      rw [uIoc_of_le hc] at hx
      refine' (continuousAt_cpow_const (Or.inl _)).comp Complex.continuous_ofReal.continuousAt
      rw [Complex.ofReal_re]
      exact hx.1
  intro c; rcases le_total 0 c with (hc | hc)
  -- ⊢ IntervalIntegrable (fun x => ↑x ^ r) volume 0 c
           -- ⊢ IntervalIntegrable (fun x => ↑x ^ r) volume 0 c
  · exact this c hc
    -- 🎉 no goals
  · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
    -- ⊢ IntervalIntegrable (fun x => ↑(-x) ^ r) volume 0 (-c)
    have m := (this (-c) (by linarith)).const_mul (Complex.exp (π * Complex.I * r))
    -- ⊢ IntervalIntegrable (fun x => ↑(-x) ^ r) volume 0 (-c)
    rw [intervalIntegrable_iff, uIoc_of_le (by linarith : 0 ≤ -c)] at m ⊢
    -- ⊢ IntegrableOn (fun x => ↑(-x) ^ r) (Set.Ioc 0 (-c))
    refine' m.congr_fun (fun x hx => _) measurableSet_Ioc
    -- ⊢ Complex.exp (↑π * Complex.I * r) * ↑x ^ r = ↑(-x) ^ r
    dsimp only
    -- ⊢ Complex.exp (↑π * Complex.I * r) * ↑x ^ r = ↑(-x) ^ r
    have : -x ≤ 0 := by linarith [hx.1]
    -- ⊢ Complex.exp (↑π * Complex.I * r) * ↑x ^ r = ↑(-x) ^ r
    rw [Complex.ofReal_cpow_of_nonpos this, mul_comm]
    -- ⊢ ↑x ^ r * Complex.exp (↑π * Complex.I * r) = (-↑(-x)) ^ r * Complex.exp (↑π * …
    simp
    -- 🎉 no goals
#align interval_integral.interval_integrable_cpow' intervalIntegral.intervalIntegrable_cpow'

@[simp]
theorem intervalIntegrable_id : IntervalIntegrable (fun x => x) μ a b :=
  continuous_id.intervalIntegrable a b
#align interval_integral.interval_integrable_id intervalIntegral.intervalIntegrable_id

-- @[simp] -- Porting note: simp can prove this
theorem intervalIntegrable_const : IntervalIntegrable (fun _ => c) μ a b :=
  continuous_const.intervalIntegrable a b
#align interval_integral.interval_integrable_const intervalIntegral.intervalIntegrable_const

theorem intervalIntegrable_one_div (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => 1 / f x) μ a b :=
  (continuousOn_const.div hf h).intervalIntegrable
#align interval_integral.interval_integrable_one_div intervalIntegral.intervalIntegrable_one_div

@[simp]
theorem intervalIntegrable_inv (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => (f x)⁻¹) μ a b := by
  simpa only [one_div] using intervalIntegrable_one_div h hf
  -- 🎉 no goals
#align interval_integral.interval_integrable_inv intervalIntegral.intervalIntegrable_inv

@[simp]
theorem intervalIntegrable_exp : IntervalIntegrable exp μ a b :=
  continuous_exp.intervalIntegrable a b
#align interval_integral.interval_integrable_exp intervalIntegral.intervalIntegrable_exp

@[simp]
theorem _root_.IntervalIntegrable.log (hf : ContinuousOn f [[a, b]])
    (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0) :
    IntervalIntegrable (fun x => log (f x)) μ a b :=
  (ContinuousOn.log hf h).intervalIntegrable
#align interval_integrable.log IntervalIntegrable.log

@[simp]
theorem intervalIntegrable_log (h : (0 : ℝ) ∉ [[a, b]]) : IntervalIntegrable log μ a b :=
  IntervalIntegrable.log continuousOn_id fun _ hx => ne_of_mem_of_not_mem hx h
#align interval_integral.interval_integrable_log intervalIntegral.intervalIntegrable_log

@[simp]
theorem intervalIntegrable_sin : IntervalIntegrable sin μ a b :=
  continuous_sin.intervalIntegrable a b
#align interval_integral.interval_integrable_sin intervalIntegral.intervalIntegrable_sin

@[simp]
theorem intervalIntegrable_cos : IntervalIntegrable cos μ a b :=
  continuous_cos.intervalIntegrable a b
#align interval_integral.interval_integrable_cos intervalIntegral.intervalIntegrable_cos

theorem intervalIntegrable_one_div_one_add_sq :
    IntervalIntegrable (fun x : ℝ => 1 / (↑1 + x ^ 2)) μ a b := by
  refine' (continuous_const.div _ fun x => _).intervalIntegrable a b
  -- ⊢ Continuous fun x => 1 + x ^ 2
  · continuity
    -- 🎉 no goals
  · nlinarith
    -- 🎉 no goals
#align interval_integral.interval_integrable_one_div_one_add_sq intervalIntegral.intervalIntegrable_one_div_one_add_sq

@[simp]
theorem intervalIntegrable_inv_one_add_sq :
    IntervalIntegrable (fun x : ℝ => (↑1 + x ^ 2)⁻¹) μ a b := by
  field_simp; exact_mod_cast intervalIntegrable_one_div_one_add_sq
  -- ⊢ IntervalIntegrable (fun x => 1 / (1 + x ^ 2)) μ a b
              -- 🎉 no goals
#align interval_integral.interval_integrable_inv_one_add_sq intervalIntegral.intervalIntegrable_inv_one_add_sq

/-! ### Integrals of the form `c * ∫ x in a..b, f (c * x + d)` -/


-- Porting note: was @[simp]; simpNF says LHS does not simplify when applying lemma on itself
theorem mul_integral_comp_mul_right : (c * ∫ x in a..b, f (x * c)) = ∫ x in a * c..b * c, f x :=
  smul_integral_comp_mul_right f c
#align interval_integral.mul_integral_comp_mul_right intervalIntegral.mul_integral_comp_mul_right

-- Porting note: was @[simp]
theorem mul_integral_comp_mul_left : (c * ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x :=
  smul_integral_comp_mul_left f c
#align interval_integral.mul_integral_comp_mul_left intervalIntegral.mul_integral_comp_mul_left

-- Porting note: was @[simp]
theorem inv_mul_integral_comp_div : (c⁻¹ * ∫ x in a..b, f (x / c)) = ∫ x in a / c..b / c, f x :=
  inv_smul_integral_comp_div f c
#align interval_integral.inv_mul_integral_comp_div intervalIntegral.inv_mul_integral_comp_div

-- Porting note: was @[simp]
theorem mul_integral_comp_mul_add :
    (c * ∫ x in a..b, f (c * x + d)) = ∫ x in c * a + d..c * b + d, f x :=
  smul_integral_comp_mul_add f c d
#align interval_integral.mul_integral_comp_mul_add intervalIntegral.mul_integral_comp_mul_add

-- Porting note: was @[simp]
theorem mul_integral_comp_add_mul :
    (c * ∫ x in a..b, f (d + c * x)) = ∫ x in d + c * a..d + c * b, f x :=
  smul_integral_comp_add_mul f c d
#align interval_integral.mul_integral_comp_add_mul intervalIntegral.mul_integral_comp_add_mul

-- Porting note: was @[simp]
theorem inv_mul_integral_comp_div_add :
    (c⁻¹ * ∫ x in a..b, f (x / c + d)) = ∫ x in a / c + d..b / c + d, f x :=
  inv_smul_integral_comp_div_add f c d
#align interval_integral.inv_mul_integral_comp_div_add intervalIntegral.inv_mul_integral_comp_div_add

-- Porting note: was @[simp]
theorem inv_mul_integral_comp_add_div :
    (c⁻¹ * ∫ x in a..b, f (d + x / c)) = ∫ x in d + a / c..d + b / c, f x :=
  inv_smul_integral_comp_add_div f c d
#align interval_integral.inv_mul_integral_comp_add_div intervalIntegral.inv_mul_integral_comp_add_div

-- Porting note: was @[simp]
theorem mul_integral_comp_mul_sub :
    (c * ∫ x in a..b, f (c * x - d)) = ∫ x in c * a - d..c * b - d, f x :=
  smul_integral_comp_mul_sub f c d
#align interval_integral.mul_integral_comp_mul_sub intervalIntegral.mul_integral_comp_mul_sub

-- Porting note: was @[simp]
theorem mul_integral_comp_sub_mul :
    (c * ∫ x in a..b, f (d - c * x)) = ∫ x in d - c * b..d - c * a, f x :=
  smul_integral_comp_sub_mul f c d
#align interval_integral.mul_integral_comp_sub_mul intervalIntegral.mul_integral_comp_sub_mul

-- Porting note: was @[simp]
theorem inv_mul_integral_comp_div_sub :
    (c⁻¹ * ∫ x in a..b, f (x / c - d)) = ∫ x in a / c - d..b / c - d, f x :=
  inv_smul_integral_comp_div_sub f c d
#align interval_integral.inv_mul_integral_comp_div_sub intervalIntegral.inv_mul_integral_comp_div_sub

-- Porting note: was @[simp]
theorem inv_mul_integral_comp_sub_div :
    (c⁻¹ * ∫ x in a..b, f (d - x / c)) = ∫ x in d - b / c..d - a / c, f x :=
  inv_smul_integral_comp_sub_div f c d
#align interval_integral.inv_mul_integral_comp_sub_div intervalIntegral.inv_mul_integral_comp_sub_div

end intervalIntegral

open intervalIntegral

/-! ### Integrals of simple functions -/


theorem integral_cpow {r : ℂ} (h : -1 < r.re ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    (∫ x : ℝ in a..b, (x : ℂ) ^ r) = ((b:ℂ) ^ (r + 1) - (a:ℂ) ^ (r + 1)) / (r + 1) := by
  rw [sub_div]
  -- ⊢ ∫ (x : ℝ) in a..b, ↑x ^ r = ↑b ^ (r + 1) / (r + 1) - ↑a ^ (r + 1) / (r + 1)
  have hr : r + 1 ≠ 0 := by
    cases' h with h h
    · apply_fun Complex.re
      rw [Complex.add_re, Complex.one_re, Complex.zero_re, Ne.def, add_eq_zero_iff_eq_neg]
      exact h.ne'
    · rw [Ne.def, ← add_eq_zero_iff_eq_neg] at h; exact h.1
  by_cases hab : (0 : ℝ) ∉ [[a, b]]
  -- ⊢ ∫ (x : ℝ) in a..b, ↑x ^ r = ↑b ^ (r + 1) / (r + 1) - ↑a ^ (r + 1) / (r + 1)
  · apply integral_eq_sub_of_hasDerivAt (fun x hx => ?_)
      (intervalIntegrable_cpow (r := r) <| Or.inr hab)
    refine' hasDerivAt_ofReal_cpow (ne_of_mem_of_not_mem hx hab) _
    -- ⊢ r ≠ -1
    contrapose! hr; rwa [add_eq_zero_iff_eq_neg]
    -- ⊢ r + 1 = 0
                    -- 🎉 no goals
  replace h : -1 < r.re; · tauto
  -- ⊢ -1 < r.re
                           -- 🎉 no goals
  suffices ∀ c : ℝ, (∫ x : ℝ in (0)..c, (x : ℂ) ^ r) =
      (c:ℂ) ^ (r + 1) / (r + 1) - (0:ℂ) ^ (r + 1) / (r + 1) by
    rw [← integral_add_adjacent_intervals (@intervalIntegrable_cpow' a 0 r h)
      (@intervalIntegrable_cpow' 0 b r h), integral_symm, this a, this b, Complex.zero_cpow hr]
    ring
  intro c
  -- ⊢ ∫ (x : ℝ) in 0 ..c, ↑x ^ r = ↑c ^ (r + 1) / (r + 1) - 0 ^ (r + 1) / (r + 1)
  apply integral_eq_sub_of_hasDeriv_right
  · refine' ((Complex.continuous_ofReal_cpow_const _).div_const _).continuousOn
    -- ⊢ 0 < (r + 1).re
    rwa [Complex.add_re, Complex.one_re, ← neg_lt_iff_pos_add]
    -- 🎉 no goals
  · refine' fun x hx => (hasDerivAt_ofReal_cpow _ _).hasDerivWithinAt
    -- ⊢ x ≠ 0
    · rcases le_total c 0 with (hc | hc)
      -- ⊢ x ≠ 0
      · rw [max_eq_left hc] at hx; exact hx.2.ne
        -- ⊢ x ≠ 0
                                   -- 🎉 no goals
      · rw [min_eq_left hc] at hx; exact hx.1.ne'
        -- ⊢ x ≠ 0
                                   -- 🎉 no goals
    · contrapose! hr; rw [hr]; ring
      -- ⊢ r + 1 = 0
                      -- ⊢ -1 + 1 = 0
                               -- 🎉 no goals
  · exact intervalIntegrable_cpow' h
    -- 🎉 no goals
#align integral_cpow integral_cpow

theorem integral_rpow {r : ℝ} (h : -1 < r ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    ∫ x in a..b, x ^ r = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  have h' : -1 < (r : ℂ).re ∨ (r : ℂ) ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]] := by
    cases h
    · left; rwa [Complex.ofReal_re]
    · right; rwa [← Complex.ofReal_one, ← Complex.ofReal_neg, Ne.def, Complex.ofReal_inj]
  have :
    (∫ x in a..b, (x : ℂ) ^ (r : ℂ)) = ((b : ℂ) ^ (r + 1 : ℂ) - (a : ℂ) ^ (r + 1 : ℂ)) / (r + 1) :=
    integral_cpow h'
  apply_fun Complex.re at this; convert this
  -- ⊢ ∫ (x : ℝ) in a..b, x ^ r = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1)
                                -- ⊢ ∫ (x : ℝ) in a..b, x ^ r = (∫ (x : ℝ) in a..b, ↑x ^ ↑r).re
  · simp_rw [intervalIntegral_eq_integral_uIoc, Complex.real_smul, Complex.ofReal_mul_re]
    -- ⊢ (if a ≤ b then 1 else -1) • ∫ (x : ℝ) in Ι a b, x ^ r = (if a ≤ b then 1 els …
    · -- Porting note: was `change ... with ...`
      have : Complex.re = IsROrC.re := by rfl
      -- ⊢ (if a ≤ b then 1 else -1) • ∫ (x : ℝ) in Ι a b, x ^ r = (if a ≤ b then 1 els …
      rw [this, ← integral_re]; rfl
      -- ⊢ (if a ≤ b then 1 else -1) • ∫ (x : ℝ) in Ι a b, x ^ r = (if a ≤ b then 1 els …
                                -- ⊢ MeasureTheory.Integrable fun x => ↑x ^ ↑r
      refine' intervalIntegrable_iff.mp _
      -- ⊢ IntervalIntegrable (fun x => ↑x ^ ↑r) MeasureTheory.volume a b
      cases' h' with h' h'
      -- ⊢ IntervalIntegrable (fun x => ↑x ^ ↑r) MeasureTheory.volume a b
      · exact intervalIntegrable_cpow' h'
        -- 🎉 no goals
      · exact intervalIntegrable_cpow (Or.inr h'.2)
        -- 🎉 no goals
  · rw [(by push_cast; rfl : (r : ℂ) + 1 = ((r + 1 : ℝ) : ℂ))]
    -- ⊢ (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) = ((↑b ^ ↑(r + 1) - ↑a ^ ↑(r + 1)) / ↑ …
    simp_rw [div_eq_inv_mul, ← Complex.ofReal_inv, Complex.ofReal_mul_re, Complex.sub_re]
    -- ⊢ (r + 1)⁻¹ * (b ^ (r + 1) - a ^ (r + 1)) = (r + 1)⁻¹ * ((↑b ^ ↑(r + 1)).re -  …
    rfl
    -- 🎉 no goals
#align integral_rpow integral_rpow

theorem integral_zpow {n : ℤ} (h : 0 ≤ n ∨ n ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  replace h : -1 < (n : ℝ) ∨ (n : ℝ) ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]; · exact_mod_cast h
  -- ⊢ -1 < ↑n ∨ ↑n ≠ -1 ∧ ¬0 ∈ [[a, b]]
                                                                  -- 🎉 no goals
  exact_mod_cast integral_rpow h
  -- 🎉 no goals
#align integral_zpow integral_zpow

@[simp]
theorem integral_pow : ∫ x in a..b, x ^ n = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  simpa only [← Int.ofNat_succ, zpow_ofNat] using integral_zpow (Or.inl (Int.coe_nat_nonneg n))
  -- 🎉 no goals
#align integral_pow integral_pow

/-- Integral of `|x - a| ^ n` over `Ι a b`. This integral appears in the proof of the
Picard-Lindelöf/Cauchy-Lipschitz theorem. -/
theorem integral_pow_abs_sub_uIoc : ∫ x in Ι a b, |x - a| ^ n = |b - a| ^ (n + 1) / (n + 1) := by
  cases' le_or_lt a b with hab hab
  -- ⊢ ∫ (x : ℝ) in Ι a b, |x - a| ^ n = |b - a| ^ (n + 1) / (↑n + 1)
  · calc
      ∫ x in Ι a b, |x - a| ^ n = ∫ x in a..b, |x - a| ^ n := by
        rw [uIoc_of_le hab, ← integral_of_le hab]
      _ = ∫ x in (0)..(b - a), x ^ n := by
        simp only [integral_comp_sub_right fun x => |x| ^ n, sub_self]
        refine' integral_congr fun x hx => congr_arg₂ Pow.pow (abs_of_nonneg <| _) rfl
        rw [uIcc_of_le (sub_nonneg.2 hab)] at hx
        exact hx.1
      _ = |b - a| ^ (n + 1) / (n + 1) := by simp [abs_of_nonneg (sub_nonneg.2 hab)]
  · calc
      ∫ x in Ι a b, |x - a| ^ n = ∫ x in b..a, |x - a| ^ n := by
        rw [uIoc_of_lt hab, ← integral_of_le hab.le]
      _ = ∫ x in b - a..0, (-x) ^ n := by
        simp only [integral_comp_sub_right fun x => |x| ^ n, sub_self]
        refine' integral_congr fun x hx => congr_arg₂ Pow.pow (abs_of_nonpos <| _) rfl
        rw [uIcc_of_le (sub_nonpos.2 hab.le)] at hx
        exact hx.2
      _ = |b - a| ^ (n + 1) / (n + 1) := by
        simp [integral_comp_neg fun x => x ^ n, abs_of_neg (sub_neg.2 hab)]
#align integral_pow_abs_sub_uIoc integral_pow_abs_sub_uIoc

@[simp]
theorem integral_id : ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 := by
  have := @integral_pow a b 1
  -- ⊢ ∫ (x : ℝ) in a..b, x = (b ^ 2 - a ^ 2) / 2
  norm_num at this
  -- ⊢ ∫ (x : ℝ) in a..b, x = (b ^ 2 - a ^ 2) / 2
  exact this
  -- 🎉 no goals
#align integral_id integral_id

-- @[simp] -- Porting note: simp can prove this
theorem integral_one : (∫ _ in a..b, (1 : ℝ)) = b - a := by
  simp only [mul_one, smul_eq_mul, integral_const]
  -- 🎉 no goals
#align integral_one integral_one

theorem integral_const_on_unit_interval : ∫ _ in a..a + 1, b = b := by simp
                                                                       -- 🎉 no goals
#align integral_const_on_unit_interval integral_const_on_unit_interval

@[simp]
theorem integral_inv (h : (0 : ℝ) ∉ [[a, b]]) : ∫ x in a..b, x⁻¹ = log (b / a) := by
  have h' := fun x (hx : x ∈ [[a, b]]) => ne_of_mem_of_not_mem hx h
  -- ⊢ ∫ (x : ℝ) in a..b, x⁻¹ = Real.log (b / a)
  rw [integral_deriv_eq_sub' _ deriv_log' (fun x hx => differentiableAt_log (h' x hx))
      (continuousOn_inv₀.mono <| subset_compl_singleton_iff.mpr h),
    log_div (h' b right_mem_uIcc) (h' a left_mem_uIcc)]
#align integral_inv integral_inv

@[simp]
theorem integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : ∫ x in a..b, x⁻¹ = log (b / a) :=
  integral_inv <| not_mem_uIcc_of_lt ha hb
#align integral_inv_of_pos integral_inv_of_pos

@[simp]
theorem integral_inv_of_neg (ha : a < 0) (hb : b < 0) : ∫ x in a..b, x⁻¹ = log (b / a) :=
  integral_inv <| not_mem_uIcc_of_gt ha hb
#align integral_inv_of_neg integral_inv_of_neg

theorem integral_one_div (h : (0 : ℝ) ∉ [[a, b]]) : ∫ x : ℝ in a..b, 1 / x = log (b / a) := by
  simp only [one_div, integral_inv h]
  -- 🎉 no goals
#align integral_one_div integral_one_div

theorem integral_one_div_of_pos (ha : 0 < a) (hb : 0 < b) :
    ∫ x : ℝ in a..b, 1 / x = log (b / a) := by simp only [one_div, integral_inv_of_pos ha hb]
                                               -- 🎉 no goals
#align integral_one_div_of_pos integral_one_div_of_pos

theorem integral_one_div_of_neg (ha : a < 0) (hb : b < 0) :
    ∫ x : ℝ in a..b, 1 / x = log (b / a) := by simp only [one_div, integral_inv_of_neg ha hb]
                                               -- 🎉 no goals
#align integral_one_div_of_neg integral_one_div_of_neg

@[simp]
theorem integral_exp : ∫ x in a..b, exp x = exp b - exp a := by
  rw [integral_deriv_eq_sub']
  · simp
    -- 🎉 no goals
  · exact fun _ _ => differentiableAt_exp
    -- 🎉 no goals
  · exact continuousOn_exp
    -- 🎉 no goals
#align integral_exp integral_exp

theorem integral_exp_mul_complex {c : ℂ} (hc : c ≠ 0) :
    (∫ x in a..b, Complex.exp (c * x)) = (Complex.exp (c * b) - Complex.exp (c * a)) / c := by
  have D : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c) (Complex.exp (c * x)) x := by
    intro x
    conv => congr
    rw [← mul_div_cancel (Complex.exp (c * x)) hc]
    apply ((Complex.hasDerivAt_exp _).comp x _).div_const c
    simpa only [mul_one] using ((hasDerivAt_id (x : ℂ)).const_mul _).comp_ofReal
  rw [integral_deriv_eq_sub' _ (funext fun x => (D x).deriv) fun x _ => (D x).differentiableAt]
  -- ⊢ Complex.exp (c * ↑b) / c - Complex.exp (c * ↑a) / c = (Complex.exp (c * ↑b)  …
  · ring
    -- 🎉 no goals
  · apply Continuous.continuousOn; continuity
    -- ⊢ Continuous fun x => Complex.exp (c * ↑x)
                                   -- 🎉 no goals
#align integral_exp_mul_complex integral_exp_mul_complex

@[simp]
theorem integral_log (h : (0 : ℝ) ∉ [[a, b]]) :
    ∫ x in a..b, log x = b * log b - a * log a - b + a := by
  have h' := fun x (hx : x ∈ [[a, b]]) => ne_of_mem_of_not_mem hx h
  -- ⊢ ∫ (x : ℝ) in a..b, Real.log x = b * Real.log b - a * Real.log a - b + a
  have heq := fun x hx => mul_inv_cancel (h' x hx)
  -- ⊢ ∫ (x : ℝ) in a..b, Real.log x = b * Real.log b - a * Real.log a - b + a
  convert integral_mul_deriv_eq_deriv_mul (fun x hx => hasDerivAt_log (h' x hx))
    (fun x _ => hasDerivAt_id x) (continuousOn_inv₀.mono <|
      subset_compl_singleton_iff.mpr h).intervalIntegrable
        continuousOn_const.intervalIntegrable using 1 <;>
  simp [integral_congr heq, mul_comm, ← sub_add]
  -- 🎉 no goals
  -- 🎉 no goals
#align integral_log integral_log

@[simp]
theorem integral_log_of_pos (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, log x = b * log b - a * log a - b + a :=
  integral_log <| not_mem_uIcc_of_lt ha hb
#align integral_log_of_pos integral_log_of_pos

@[simp]
theorem integral_log_of_neg (ha : a < 0) (hb : b < 0) :
    ∫ x in a..b, log x = b * log b - a * log a - b + a :=
  integral_log <| not_mem_uIcc_of_gt ha hb
#align integral_log_of_neg integral_log_of_neg

@[simp]
theorem integral_sin : ∫ x in a..b, sin x = cos a - cos b := by
  rw [integral_deriv_eq_sub' fun x => -cos x]
  · ring
    -- 🎉 no goals
  · norm_num
    -- 🎉 no goals
  · simp only [differentiableAt_neg_iff, differentiableAt_cos, implies_true]
    -- 🎉 no goals
  · exact continuousOn_sin
    -- 🎉 no goals
#align integral_sin integral_sin

@[simp]
theorem integral_cos : ∫ x in a..b, cos x = sin b - sin a := by
  rw [integral_deriv_eq_sub']
  · norm_num
    -- 🎉 no goals
  · simp only [differentiableAt_sin, implies_true]
    -- 🎉 no goals
  · exact continuousOn_cos
    -- 🎉 no goals
#align integral_cos integral_cos

theorem integral_cos_mul_complex {z : ℂ} (hz : z ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Complex.cos (z * x)) = Complex.sin (z * b) / z - Complex.sin (z * a) / z := by
  apply integral_eq_sub_of_hasDerivAt
  -- ⊢ ∀ (x : ℝ), x ∈ [[a, b]] → HasDerivAt (fun b => Complex.sin (z * ↑b) / z) (Co …
  swap
  -- ⊢ IntervalIntegrable (fun y => Complex.cos (z * ↑y)) MeasureTheory.volume a b
  · apply Continuous.intervalIntegrable
    -- ⊢ Continuous fun y => Complex.cos (z * ↑y)
    exact Complex.continuous_cos.comp (continuous_const.mul Complex.continuous_ofReal)
    -- 🎉 no goals
  intro x _
  -- ⊢ HasDerivAt (fun b => Complex.sin (z * ↑b) / z) (Complex.cos (z * ↑x)) x
  have a := Complex.hasDerivAt_sin (↑x * z)
  -- ⊢ HasDerivAt (fun b => Complex.sin (z * ↑b) / z) (Complex.cos (z * ↑x)) x
  have b : HasDerivAt (fun y => y * z : ℂ → ℂ) z ↑x := hasDerivAt_mul_const _
  -- ⊢ HasDerivAt (fun b => Complex.sin (z * ↑b) / z) (Complex.cos (z * ↑x)) x
  have c : HasDerivAt (fun y : ℂ => Complex.sin (y * z)) _ ↑x := HasDerivAt.comp (𝕜 := ℂ) x a b
  -- ⊢ HasDerivAt (fun b => Complex.sin (z * ↑b) / z) (Complex.cos (z * ↑x)) x
  have d := HasDerivAt.comp_ofReal (c.div_const z)
  -- ⊢ HasDerivAt (fun b => Complex.sin (z * ↑b) / z) (Complex.cos (z * ↑x)) x
  simp only [mul_comm] at d
  -- ⊢ HasDerivAt (fun b => Complex.sin (z * ↑b) / z) (Complex.cos (z * ↑x)) x
  convert d using 1
  -- ⊢ Complex.cos (z * ↑x) = z * Complex.cos (z * ↑x) / z
  conv_rhs => arg 1; rw [mul_comm]
  -- ⊢ Complex.cos (z * ↑x) = Complex.cos (z * ↑x) * z / z
  rw [mul_div_cancel _ hz]
  -- 🎉 no goals
#align integral_cos_mul_complex integral_cos_mul_complex

theorem integral_cos_sq_sub_sin_sq :
    ∫ x in a..b, cos x ^ 2 - sin x ^ 2 = sin b * cos b - sin a * cos a := by
  simpa only [sq, sub_eq_add_neg, neg_mul_eq_mul_neg] using
    integral_deriv_mul_eq_sub (fun x _ => hasDerivAt_sin x) (fun x _ => hasDerivAt_cos x)
      continuousOn_cos.intervalIntegrable continuousOn_sin.neg.intervalIntegrable
#align integral_cos_sq_sub_sin_sq integral_cos_sq_sub_sin_sq

@[simp]
theorem integral_inv_one_add_sq : (∫ x : ℝ in a..b, (↑1 + x ^ 2)⁻¹) = arctan b - arctan a := by
  simp only [← one_div]
  -- ⊢ ∫ (x : ℝ) in a..b, 1 / (1 + x ^ 2) = arctan b - arctan a
  refine' integral_deriv_eq_sub' _ _ _ (continuous_const.div _ fun x => _).continuousOn
  · norm_num
    -- 🎉 no goals
  · exact fun _ _ => differentiableAt_arctan _
    -- 🎉 no goals
  · continuity
    -- 🎉 no goals
  · nlinarith
    -- 🎉 no goals
#align integral_inv_one_add_sq integral_inv_one_add_sq

theorem integral_one_div_one_add_sq :
    (∫ x : ℝ in a..b, ↑1 / (↑1 + x ^ 2)) = arctan b - arctan a := by
  simp only [one_div, integral_inv_one_add_sq]
  -- 🎉 no goals
#align integral_one_div_one_add_sq integral_one_div_one_add_sq

section RpowCpow

open Complex

theorem integral_mul_cpow_one_add_sq {t : ℂ} (ht : t ≠ -1) :
    (∫ x : ℝ in a..b, (x : ℂ) * ((1:ℂ) + ↑x ^ 2) ^ t) =
      ((1:ℂ) + (b:ℂ) ^ 2) ^ (t + 1) / (2 * (t + ↑1)) -
      ((1:ℂ) + (a:ℂ) ^ 2) ^ (t + 1) / (2 * (t + ↑1)) := by
  have : t + 1 ≠ 0 := by contrapose! ht; rwa [add_eq_zero_iff_eq_neg] at ht
  -- ⊢ ∫ (x : ℝ) in a..b, ↑x * (1 + ↑x ^ 2) ^ t = (1 + ↑b ^ 2) ^ (t + 1) / (↑2 * (t …
  apply integral_eq_sub_of_hasDerivAt
  -- ⊢ ∀ (x : ℝ), x ∈ [[a, b]] → HasDerivAt (fun {b} => (1 + ↑b ^ 2) ^ (t + 1) / (↑ …
  · intro x _
    -- ⊢ HasDerivAt (fun {b} => (1 + ↑b ^ 2) ^ (t + 1) / (↑2 * (t + 1))) (↑x * (1 + ↑ …
    have f : HasDerivAt (fun y : ℂ => 1 + y ^ 2) (2 * x) x := by
      convert (hasDerivAt_pow 2 (x : ℂ)).const_add 1
      · norm_cast
      · simp
    have g :
      ∀ {z : ℂ}, 0 < z.re → HasDerivAt (fun z => z ^ (t + 1) / (2 * (t + 1))) (z ^ t / 2) z := by
      intro z hz
      convert (HasDerivAt.cpow_const (c := t + 1) (hasDerivAt_id _)
        (Or.inl hz)).div_const (2 * (t + 1)) using 1
      field_simp
      ring
    convert (HasDerivAt.comp (↑x) (g _) f).comp_ofReal using 1
    · simp
      -- 🎉 no goals
    · field_simp; ring
      -- ⊢ ↑x * (1 + ↑x ^ 2) ^ t * 2 = (1 + ↑x ^ 2) ^ t * (2 * ↑x)
                  -- 🎉 no goals
    · exact_mod_cast add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg x)
      -- 🎉 no goals
  · apply Continuous.intervalIntegrable
    -- ⊢ Continuous fun y => ↑y * (1 + ↑y ^ 2) ^ t
    refine' continuous_ofReal.mul _
    -- ⊢ Continuous fun y => (1 + ↑y ^ 2) ^ t
    apply Continuous.cpow
    · exact continuous_const.add (continuous_ofReal.pow 2)
      -- 🎉 no goals
    · exact continuous_const
      -- 🎉 no goals
    · intro a
      -- ⊢ 0 < (1 + ↑a ^ 2).re ∨ (1 + ↑a ^ 2).im ≠ 0
      rw [add_re, one_re, ← ofReal_pow, ofReal_re]
      -- ⊢ 0 < 1 + a ^ 2 ∨ (1 + ↑(a ^ 2)).im ≠ 0
      exact Or.inl (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg a))
      -- 🎉 no goals
#align integral_mul_cpow_one_add_sq integral_mul_cpow_one_add_sq

theorem integral_mul_rpow_one_add_sq {t : ℝ} (ht : t ≠ -1) :
    (∫ x : ℝ in a..b, x * (↑1 + x ^ 2) ^ t) =
      (↑1 + b ^ 2) ^ (t + 1) / (↑2 * (t + ↑1)) - (↑1 + a ^ 2) ^ (t + 1) / (↑2 * (t + ↑1)) := by
  have : ∀ x s : ℝ, (((↑1 + x ^ 2) ^ s : ℝ) : ℂ) = (1 + (x : ℂ) ^ 2) ^ (s:ℂ) := by
    intro x s
    norm_cast
    rw [ofReal_cpow, ofReal_add, ofReal_pow, ofReal_one]
    exact add_nonneg zero_le_one (sq_nonneg x)
  rw [← ofReal_inj]
  -- ⊢ ↑(∫ (x : ℝ) in a..b, x * (1 + x ^ 2) ^ t) = ↑((1 + b ^ 2) ^ (t + 1) / (2 * ( …
  convert integral_mul_cpow_one_add_sq (_ : (t : ℂ) ≠ -1)
  · rw [← intervalIntegral.integral_ofReal]
    congr with x : 1
    -- ⊢ ↑(x * (1 + x ^ 2) ^ t) = ↑x * (1 + ↑x ^ 2) ^ ↑t
    rw [ofReal_mul, this x t]
    -- ⊢ ↑x * (↑1 + ↑x ^ 2) ^ ↑t = ↑x * (1 + ↑x ^ 2) ^ ↑t
    norm_cast
    -- 🎉 no goals
  · simp_rw [ofReal_sub, ofReal_div, this a (t + 1), this b (t + 1)]
    -- ⊢ (↑1 + ↑b ^ 2) ^ ↑(t + 1) / ↑(2 * (t + 1)) - (↑1 + ↑a ^ 2) ^ ↑(t + 1) / ↑(2 * …
    push_cast; rfl
    -- ⊢ (1 + ↑b ^ 2) ^ (↑t + 1) / (2 * (↑t + 1)) - (1 + ↑a ^ 2) ^ (↑t + 1) / (2 * (↑ …
               -- 🎉 no goals
  · rw [← ofReal_one, ← ofReal_neg, Ne.def, ofReal_inj]
    -- ⊢ ¬t = -1
    exact ht
    -- 🎉 no goals
#align integral_mul_rpow_one_add_sq integral_mul_rpow_one_add_sq

end RpowCpow

/-! ### Integral of `sin x ^ n` -/


theorem integral_sin_pow_aux :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b + (↑n + 1) * ∫ x in a..b, sin x ^ n) -
        (↑n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
  have continuous_sin_pow : ∀ (k : ℕ), (Continuous fun x => sin x ^ k) :=
    fun k => continuous_sin.pow k
  let C := sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b
  -- ⊢ ∫ (x : ℝ) in a..b, sin x ^ (n + 2) = (sin a ^ (n + 1) * cos a - sin b ^ (n + …
  have h : ∀ α β γ : ℝ, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  -- ⊢ ∫ (x : ℝ) in a..b, sin x ^ (n + 2) = (sin a ^ (n + 1) * cos a - sin b ^ (n + …
  have hu : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => sin y ^ (n + 1)) ((n + 1 : ℕ) * cos x * sin x ^ n) x :=
    fun x _ => by simpa only [mul_right_comm] using (hasDerivAt_sin x).pow (n + 1)
  have hv : ∀ x ∈ [[a, b]], HasDerivAt (-cos) (sin x) x := fun x _ => by
    simpa only [neg_neg] using (hasDerivAt_cos x).neg
  have H := integral_mul_deriv_eq_deriv_mul hu hv ?_ ?_
  calc
    (∫ x in a..b, sin x ^ (n + 2)) = ∫ x in a..b, sin x ^ (n + 1) * sin x := by
      simp only [_root_.pow_succ']
    _ = C + (↑n + 1) * ∫ x in a..b, cos x ^ 2 * sin x ^ n := by simp [H, h, sq]; ring
    _ = C + (↑n + 1) * ∫ x in a..b, sin x ^ n - sin x ^ (n + 2) := by
      simp [cos_sq', sub_mul, ← pow_add, add_comm]
    _ = (C + (↑n + 1) * ∫ x in a..b, sin x ^ n) - (↑n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
      rw [integral_sub, mul_sub, add_sub_assoc] <;> apply Continuous.intervalIntegrable
      -- Porting note: was `... <;> continuity`
      · exact continuous_sin_pow n
      · exact continuous_sin_pow (n + 2)
  all_goals apply Continuous.intervalIntegrable
  -- ⊢ Continuous fun x => ↑(n + 1) * cos x * sin x ^ n
  -- Porting note: was `... <;> continuity`
  · have : Continuous fun x ↦ ↑(n + 1) * cos x := by continuity
    -- ⊢ Continuous fun x => ↑(n + 1) * cos x * sin x ^ n
    exact this.mul (continuous_sin_pow n)
    -- 🎉 no goals
  · exact continuous_sin
    -- 🎉 no goals
#align integral_sin_pow_aux integral_sin_pow_aux

/-- The reduction formula for the integral of `sin x ^ n` for any natural `n ≥ 2`. -/
theorem integral_sin_pow :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b) / (n + 2) +
        (n + 1) / (n + 2) * ∫ x in a..b, sin x ^ n := by
  have : n + 2 ≠ 0 := by linarith
  -- ⊢ ∫ (x : ℝ) in a..b, sin x ^ (n + 2) = (sin a ^ (n + 1) * cos a - sin b ^ (n + …
  have : (n : ℝ) + 2 ≠ 0 := by norm_cast
  -- ⊢ ∫ (x : ℝ) in a..b, sin x ^ (n + 2) = (sin a ^ (n + 1) * cos a - sin b ^ (n + …
  field_simp
  -- ⊢ (∫ (x : ℝ) in a..b, sin x ^ (n + 2)) * (↑n + 2) = sin a ^ (n + 1) * cos a -  …
  convert eq_sub_iff_add_eq.mp (integral_sin_pow_aux n) using 1
  -- ⊢ (∫ (x : ℝ) in a..b, sin x ^ (n + 2)) * (↑n + 2) = (∫ (x : ℝ) in a..b, sin x  …
  ring
  -- 🎉 no goals
#align integral_sin_pow integral_sin_pow

@[simp]
theorem integral_sin_sq : ∫ x in a..b, sin x ^ 2 = (sin a * cos a - sin b * cos b + b - a) / 2 :=
  by field_simp [integral_sin_pow, add_sub_assoc]
     -- 🎉 no goals
#align integral_sin_sq integral_sin_sq

theorem integral_sin_pow_odd :
    (∫ x in (0)..π, sin x ^ (2 * n + 1)) = 2 * ∏ i in range n, (2 * (i:ℝ) + 2) / (2 * i + 3) := by
  induction' n with k ih; · norm_num
  -- ⊢ ∫ (x : ℝ) in 0 ..π, sin x ^ (2 * zero + 1) = 2 * ∏ i in Finset.range zero, ( …
                            -- 🎉 no goals
  rw [prod_range_succ_comm, mul_left_comm, ← ih, mul_succ, integral_sin_pow]
  -- ⊢ (sin 0 ^ (2 * k + 1 + 1) * cos 0 - sin π ^ (2 * k + 1 + 1) * cos π) / (↑(2 * …
  norm_cast
  -- ⊢ (sin 0 ^ (2 * k + 1 + 1) * cos 0 - sin π ^ (2 * k + 1 + 1) * cos π) / ↑(2 *  …
  simp [-cast_add, field_simps]
  -- 🎉 no goals
#align integral_sin_pow_odd integral_sin_pow_odd

theorem integral_sin_pow_even :
    (∫ x in (0)..π, sin x ^ (2 * n)) = π * ∏ i in range n, (2 * (i:ℝ) + 1) / (2 * i + 2) := by
  induction' n with k ih; · simp
  -- ⊢ ∫ (x : ℝ) in 0 ..π, sin x ^ (2 * zero) = π * ∏ i in Finset.range zero, (2 *  …
                            -- 🎉 no goals
  rw [prod_range_succ_comm, mul_left_comm, ← ih, mul_succ, integral_sin_pow]
  -- ⊢ (sin 0 ^ (2 * k + 1) * cos 0 - sin π ^ (2 * k + 1) * cos π) / (↑(2 * k) + 2) …
  norm_cast
  -- ⊢ (sin 0 ^ (2 * k + 1) * cos 0 - sin π ^ (2 * k + 1) * cos π) / ↑(2 * k + 2) + …
  simp [-cast_add, field_simps]
  -- 🎉 no goals
#align integral_sin_pow_even integral_sin_pow_even

theorem integral_sin_pow_pos : 0 < ∫ x in (0)..π, sin x ^ n := by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩ <;>
  -- ⊢ 0 < ∫ (x : ℝ) in 0 ..π, sin x ^ (2 * k)
  simp only [integral_sin_pow_even, integral_sin_pow_odd] <;>
  -- ⊢ 0 < π * ∏ i in Finset.range k, (2 * ↑i + 1) / (2 * ↑i + 2)
  -- ⊢ 0 < 2 * ∏ i in Finset.range k, (2 * ↑i + 2) / (2 * ↑i + 3)
  refine' mul_pos (by norm_num [pi_pos]) (prod_pos fun n _ => div_pos _ _) <;>
  -- ⊢ 0 < 2 * ↑n + 1
  -- ⊢ 0 < 2 * ↑n + 2
  norm_cast <;>
  -- ⊢ 0 < 2 * n + 1
  -- ⊢ 0 < 2 * n + 2
  -- ⊢ 0 < 2 * n + 2
  -- ⊢ 0 < 2 * n + 3
  linarith
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
  -- 🎉 no goals
#align integral_sin_pow_pos integral_sin_pow_pos

theorem integral_sin_pow_succ_le : (∫ x in (0)..π, sin x ^ (n + 1)) ≤ ∫ x in (0)..π, sin x ^ n := by
  let H x h := pow_le_pow_of_le_one (sin_nonneg_of_mem_Icc h) (sin_le_one x) (n.le_add_right 1)
  -- ⊢ ∫ (x : ℝ) in 0 ..π, sin x ^ (n + 1) ≤ ∫ (x : ℝ) in 0 ..π, sin x ^ n
  refine' integral_mono_on pi_pos.le _ _ H <;> exact (continuous_sin.pow _).intervalIntegrable 0 π
  -- ⊢ IntervalIntegrable (fun x => sin x ^ (n + 1)) MeasureTheory.volume 0 π
                                               -- 🎉 no goals
                                               -- 🎉 no goals
#align integral_sin_pow_succ_le integral_sin_pow_succ_le

theorem integral_sin_pow_antitone : Antitone fun n : ℕ => ∫ x in (0)..π, sin x ^ n :=
  antitone_nat_of_succ_le integral_sin_pow_succ_le
#align integral_sin_pow_antitone integral_sin_pow_antitone

/-! ### Integral of `cos x ^ n` -/


theorem integral_cos_pow_aux :
    (∫ x in a..b, cos x ^ (n + 2)) =
      (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a + (n + 1) * ∫ x in a..b, cos x ^ n) -
        (n + 1) * ∫ x in a..b, cos x ^ (n + 2) := by
  have continuous_cos_pow : ∀ (k : ℕ), (Continuous fun x => cos x ^ k) :=
    fun k => continuous_cos.pow k
  let C := cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a
  -- ⊢ ∫ (x : ℝ) in a..b, cos x ^ (n + 2) = (cos b ^ (n + 1) * sin b - cos a ^ (n + …
  have h : ∀ α β γ : ℝ, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  -- ⊢ ∫ (x : ℝ) in a..b, cos x ^ (n + 2) = (cos b ^ (n + 1) * sin b - cos a ^ (n + …
  have hu : ∀ x ∈ [[a, b]],
      HasDerivAt (fun y => cos y ^ (n + 1)) (-(n + 1 : ℕ) * sin x * cos x ^ n) x :=
    fun x _ => by
      simpa only [mul_right_comm, neg_mul, mul_neg] using (hasDerivAt_cos x).pow (n + 1)
  have hv : ∀ x ∈ [[a, b]], HasDerivAt sin (cos x) x := fun x _ => hasDerivAt_sin x
  -- ⊢ ∫ (x : ℝ) in a..b, cos x ^ (n + 2) = (cos b ^ (n + 1) * sin b - cos a ^ (n + …
  have H := integral_mul_deriv_eq_deriv_mul hu hv ?_ ?_
  calc
    (∫ x in a..b, cos x ^ (n + 2)) = ∫ x in a..b, cos x ^ (n + 1) * cos x := by
      simp only [_root_.pow_succ']
    _ = C + (n + 1) * ∫ x in a..b, sin x ^ 2 * cos x ^ n := by simp [H, h, sq, -neg_add_rev]
    _ = C + (n + 1) * ∫ x in a..b, cos x ^ n - cos x ^ (n + 2) := by
      simp [sin_sq, sub_mul, ← pow_add, add_comm]
    _ = (C + (n + 1) * ∫ x in a..b, cos x ^ n) - (n + 1) * ∫ x in a..b, cos x ^ (n + 2) := by
      rw [integral_sub, mul_sub, add_sub_assoc] <;> apply Continuous.intervalIntegrable
      -- Porting note: was `... <;> continuity`
      · exact continuous_cos_pow n
      · exact continuous_cos_pow (n + 2)
  all_goals apply Continuous.intervalIntegrable; continuity
  -- 🎉 no goals
#align integral_cos_pow_aux integral_cos_pow_aux

/-- The reduction formula for the integral of `cos x ^ n` for any natural `n ≥ 2`. -/
theorem integral_cos_pow :
    (∫ x in a..b, cos x ^ (n + 2)) =
      (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a) / (n + 2) +
        (n + 1) / (n + 2) * ∫ x in a..b, cos x ^ n := by
  have : n + 2 ≠ 0 := by linarith
  -- ⊢ ∫ (x : ℝ) in a..b, cos x ^ (n + 2) = (cos b ^ (n + 1) * sin b - cos a ^ (n + …
  have : (n : ℝ) + 2 ≠ 0 := by norm_cast
  -- ⊢ ∫ (x : ℝ) in a..b, cos x ^ (n + 2) = (cos b ^ (n + 1) * sin b - cos a ^ (n + …
  field_simp
  -- ⊢ (∫ (x : ℝ) in a..b, cos x ^ (n + 2)) * (↑n + 2) = cos b ^ (n + 1) * sin b -  …
  convert eq_sub_iff_add_eq.mp (integral_cos_pow_aux n) using 1
  -- ⊢ (∫ (x : ℝ) in a..b, cos x ^ (n + 2)) * (↑n + 2) = (∫ (x : ℝ) in a..b, cos x  …
  ring
  -- 🎉 no goals
#align integral_cos_pow integral_cos_pow

@[simp]
theorem integral_cos_sq : ∫ x in a..b, cos x ^ 2 = (cos b * sin b - cos a * sin a + b - a) / 2 :=
  by field_simp [integral_cos_pow, add_sub_assoc]
     -- 🎉 no goals
#align integral_cos_sq integral_cos_sq

/-! ### Integral of `sin x ^ m * cos x ^ n` -/


/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `n` is odd. -/
theorem integral_sin_pow_mul_cos_pow_odd (m n : ℕ) :
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) = ∫ u in sin a..sin b, u^m * (↑1 - u ^ 2) ^ n :=
  have hc : Continuous fun u : ℝ => u ^ m * (↑1 - u ^ 2) ^ n := -- Porting note: was `by continuity`
    (continuous_pow m).mul ((continuous_const.sub (continuous_pow 2)).pow n)
  calc
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) =
        ∫ x in a..b, sin x ^ m * (↑1 - sin x ^ 2) ^ n * cos x := by
      simp only [_root_.pow_zero, _root_.pow_succ', mul_assoc, pow_mul, one_mul]
      -- ⊢ ∫ (x : ℝ) in a..b, sin x ^ m * ((cos x * cos x) ^ n * cos x) = ∫ (x : ℝ) in  …
      congr! 5
      -- ⊢ cos x✝ * cos x✝ = 1 - sin x✝ * sin x✝
      rw [← sq, ← sq, cos_sq']
      -- 🎉 no goals
    _ = ∫ u in sin a..sin b, u ^ m * (↑1 - u ^ 2) ^ n :=
      integral_comp_mul_deriv (fun x _ => hasDerivAt_sin x) continuousOn_cos hc
#align integral_sin_pow_mul_cos_pow_odd integral_sin_pow_mul_cos_pow_odd

/-- The integral of `sin x * cos x`, given in terms of sin².
  See `integral_sin_mul_cos₂` below for the integral given in terms of cos². -/
@[simp]
theorem integral_sin_mul_cos₁ : ∫ x in a..b, sin x * cos x = (sin b ^ 2 - sin a ^ 2) / 2 := by
  simpa using integral_sin_pow_mul_cos_pow_odd 1 0
  -- 🎉 no goals
#align integral_sin_mul_cos₁ integral_sin_mul_cos₁

@[simp]
theorem integral_sin_sq_mul_cos :
    ∫ x in a..b, sin x ^ 2 * cos x = (sin b ^ 3 - sin a ^ 3) / 3 := by
  have := @integral_sin_pow_mul_cos_pow_odd a b 2 0
  -- ⊢ ∫ (x : ℝ) in a..b, sin x ^ 2 * cos x = (sin b ^ 3 - sin a ^ 3) / 3
  norm_num at this; exact this
  -- ⊢ ∫ (x : ℝ) in a..b, sin x ^ 2 * cos x = (sin b ^ 3 - sin a ^ 3) / 3
                    -- 🎉 no goals
#align integral_sin_sq_mul_cos integral_sin_sq_mul_cos

@[simp]
theorem integral_cos_pow_three :
    ∫ x in a..b, cos x ^ 3 = sin b - sin a - (sin b ^ 3 - sin a ^ 3) / 3 := by
  have := @integral_sin_pow_mul_cos_pow_odd a b 0 1
  -- ⊢ ∫ (x : ℝ) in a..b, cos x ^ 3 = sin b - sin a - (sin b ^ 3 - sin a ^ 3) / 3
  norm_num at this; exact this
  -- ⊢ ∫ (x : ℝ) in a..b, cos x ^ 3 = sin b - sin a - (sin b ^ 3 - sin a ^ 3) / 3
                    -- 🎉 no goals
#align integral_cos_pow_three integral_cos_pow_three

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` is odd. -/
theorem integral_sin_pow_odd_mul_cos_pow (m n : ℕ) :
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) = ∫ u in cos b..cos a, u^n * (↑1 - u ^ 2) ^ m :=
  have hc : Continuous fun u : ℝ => u ^ n * (↑1 - u ^ 2) ^ m := -- Porting note: was `by continuity`
    (continuous_pow n).mul ((continuous_const.sub (continuous_pow 2)).pow m)
  calc
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) =
        -∫ x in b..a, sin x ^ (2 * m + 1) * cos x ^ n :=
      by rw [integral_symm]
         -- 🎉 no goals
    _ = ∫ x in b..a, (↑1 - cos x ^ 2) ^ m * -sin x * cos x ^ n := by
      simp only [_root_.pow_succ', pow_mul, _root_.pow_zero, one_mul, mul_neg, neg_mul,
        integral_neg, neg_inj]
      congr! 5
      -- ⊢ sin x✝ * sin x✝ = 1 - cos x✝ * cos x✝
      rw [← sq, ← sq, sin_sq]
      -- 🎉 no goals
    _ = ∫ x in b..a, cos x ^ n * (↑1 - cos x ^ 2) ^ m * -sin x := by congr; ext; ring
                                                                     -- ⊢ (fun x => (1 - cos x ^ 2) ^ m * -sin x * cos x ^ n) = fun x => cos x ^ n * ( …
                                                                            -- ⊢ (1 - cos x✝ ^ 2) ^ m * -sin x✝ * cos x✝ ^ n = cos x✝ ^ n * (1 - cos x✝ ^ 2)  …
                                                                                 -- 🎉 no goals
    _ = ∫ u in cos b..cos a, u ^ n * (↑1 - u ^ 2) ^ m :=
      integral_comp_mul_deriv (fun x _ => hasDerivAt_cos x) continuousOn_sin.neg hc
#align integral_sin_pow_odd_mul_cos_pow integral_sin_pow_odd_mul_cos_pow

/-- The integral of `sin x * cos x`, given in terms of cos².
See `integral_sin_mul_cos₁` above for the integral given in terms of sin². -/
theorem integral_sin_mul_cos₂ : ∫ x in a..b, sin x * cos x = (cos a ^ 2 - cos b ^ 2) / 2 := by
  simpa using integral_sin_pow_odd_mul_cos_pow 0 1
  -- 🎉 no goals
#align integral_sin_mul_cos₂ integral_sin_mul_cos₂

@[simp]
theorem integral_sin_mul_cos_sq :
    ∫ x in a..b, sin x * cos x ^ 2 = (cos a ^ 3 - cos b ^ 3) / 3 := by
  have := @integral_sin_pow_odd_mul_cos_pow a b 0 2
  -- ⊢ ∫ (x : ℝ) in a..b, sin x * cos x ^ 2 = (cos a ^ 3 - cos b ^ 3) / 3
  norm_num at this; exact this
  -- ⊢ ∫ (x : ℝ) in a..b, sin x * cos x ^ 2 = (cos a ^ 3 - cos b ^ 3) / 3
                    -- 🎉 no goals
#align integral_sin_mul_cos_sq integral_sin_mul_cos_sq

@[simp]
theorem integral_sin_pow_three :
    ∫ x in a..b, sin x ^ 3 = cos a - cos b - (cos a ^ 3 - cos b ^ 3) / 3 := by
  have := @integral_sin_pow_odd_mul_cos_pow a b 1 0
  -- ⊢ ∫ (x : ℝ) in a..b, sin x ^ 3 = cos a - cos b - (cos a ^ 3 - cos b ^ 3) / 3
  norm_num at this; exact this
  -- ⊢ ∫ (x : ℝ) in a..b, sin x ^ 3 = cos a - cos b - (cos a ^ 3 - cos b ^ 3) / 3
                    -- 🎉 no goals
#align integral_sin_pow_three integral_sin_pow_three

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` and `n` are both even. -/
theorem integral_sin_pow_even_mul_cos_pow_even (m n : ℕ) :
    (∫ x in a..b, sin x ^ (2 * m) * cos x ^ (2 * n)) =
      ∫ x in a..b, ((1 - cos (2 * x)) / 2) ^ m * ((1 + cos (2 * x)) / 2) ^ n :=
  by field_simp [pow_mul, sin_sq, cos_sq, ← sub_sub, (by ring : (2 : ℝ) - 1 = 1)]
     -- 🎉 no goals
#align integral_sin_pow_even_mul_cos_pow_even integral_sin_pow_even_mul_cos_pow_even

@[simp]
theorem integral_sin_sq_mul_cos_sq :
    ∫ x in a..b, sin x ^ 2 * cos x ^ 2 = (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 := by
  convert integral_sin_pow_even_mul_cos_pow_even 1 1 using 1
  -- ⊢ (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 = ∫ (x : ℝ) in a..b, ((1 - co …
  have h1 : ∀ c : ℝ, (↑1 - c) / ↑2 * ((↑1 + c) / ↑2) = (↑1 - c ^ 2) / 4 := fun c => by ring
  -- ⊢ (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 = ∫ (x : ℝ) in a..b, ((1 - co …
  have h2 : Continuous fun x => cos (2 * x) ^ 2 := by continuity
  -- ⊢ (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 = ∫ (x : ℝ) in a..b, ((1 - co …
  have h3 : ∀ x, cos x * sin x = sin (2 * x) / 2 := by intro; rw [sin_two_mul]; ring
  -- ⊢ (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 = ∫ (x : ℝ) in a..b, ((1 - co …
  have h4 : ∀ d : ℝ, 2 * (2 * d) = 4 * d := fun d => by ring
  -- ⊢ (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 = ∫ (x : ℝ) in a..b, ((1 - co …
  -- Porting note: was
  -- `simp [h1, h2.interval_integrable, integral_comp_mul_left fun x => cos x ^ 2, h3, h4]`
  -- `ring`
  simp only [pow_one, h1]
  -- ⊢ (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 = ∫ (x : ℝ) in a..b, (1 - cos …
  rw [integral_div, integral_sub, integral_one]
  · simp [integral_comp_mul_left (fun x => cos x ^ 2), h3, h4]; ring
    -- ⊢ (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 = (b - a - 2⁻¹ * ((sin (4 * b …
                                                                -- 🎉 no goals
  · exact intervalIntegrable_const
    -- 🎉 no goals
  · exact h2.intervalIntegrable a b
    -- 🎉 no goals
#align integral_sin_sq_mul_cos_sq integral_sin_sq_mul_cos_sq
