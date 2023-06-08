/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson

! This file was ported from Lean 3 source module analysis.special_functions.integrals
! leanprover-community/mathlib commit 011cafb4a5bc695875d186e245d6b3df03bf6c40
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

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

variable {a b : ℝ} (n : ℕ)

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y) -- Porting note: See Lean 4issue #2220

namespace intervalIntegral

open MeasureTheory

variable {f : ℝ → ℝ} {μ ν : Measure ℝ} [IsLocallyFiniteMeasure μ] (c d : ℝ)

/-! ### Interval integrability -/

@[simp]
theorem intervalIntegrable_pow : IntervalIntegrable (· ^ n) μ a b :=
  (continuous_pow n).intervalIntegrable a b
#align interval_integral.interval_integrable_pow intervalIntegral.intervalIntegrable_pow

theorem intervalIntegrable_zpow {n : ℤ} (h : 0 ≤ n ∨ (0 : ℝ) ∉ [[a, b]]) :
    IntervalIntegrable (fun x => x ^ n) μ a b :=
  (continuousOn_id.zpow₀ n fun x hx => h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable
#align interval_integral.interval_integrable_zpow intervalIntegral.intervalIntegrable_zpow

/-- See `interval_integrable_rpow'` for a version with a weaker hypothesis on `r`, but assuming the
measure is volume. -/
theorem intervalIntegrable_rpow {r : ℝ} (h : 0 ≤ r ∨ (0 : ℝ) ∉ [[a, b]]) :
    IntervalIntegrable (fun x => x ^ r) μ a b :=
  (continuousOn_id.rpow_const fun x hx =>
      h.symm.imp (ne_of_mem_of_not_mem hx) id).intervalIntegrable
#align interval_integral.interval_integrable_rpow intervalIntegral.intervalIntegrable_rpow

/-- See `interval_integrable_rpow` for a version applying to any locally finite measure, but with a
stronger hypothesis on `r`. -/
theorem intervalIntegrable_rpow' {r : ℝ} (h : -1 < r) :
    IntervalIntegrable (fun x => x ^ r) volume a b := by
  suffices ∀ c : ℝ, IntervalIntegrable (fun x => x ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x => x ^ r) volume 0 c := by
    intro c hc
    rw [intervalIntegrable_iff, uIoc_of_le hc]
    have hderiv : ∀ x ∈ Ioo 0 c, HasDerivAt (fun x : ℝ => x ^ (r + 1) / (r + 1)) (x ^ r) x := by
      intro x hx; convert (Real.hasDerivAt_rpow_const (Or.inl hx.1.ne')).div_const (r + 1)
      field_simp [(by linarith : r + 1 ≠ 0)]; ring
    apply integrable_on_deriv_of_nonneg _ hderiv
    · intro x hx; apply rpow_nonneg_of_nonneg hx.1.le
    · refine' (continuous_on_id.rpow_const _).div_const _; intro x hx; right; linarith
  intro c; rcases le_total 0 c with (hc | hc)
  · exact this c hc
  · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
    have m := (this (-c) (by linarith)).smul (cos (r * π))
    rw [intervalIntegrable_iff] at m ⊢
    refine' m.congr_fun _ measurableSet_Ioc; intro x hx
    rw [uIoc_of_le (by linarith : 0 ≤ -c)] at hx 
    simp only [Pi.smul_apply, Algebra.id.smul_eq_mul, log_neg_eq_log, mul_comm,
      rpow_def_of_pos hx.1, rpow_def_of_neg (by linarith [hx.1] : -x < 0)]
#align interval_integral.interval_integrable_rpow' intervalIntegral.intervalIntegrable_rpow'

/-- See `interval_integrable_cpow'` for a version with a weaker hypothesis on `r`, but assuming the
measure is volume. -/
theorem intervalIntegrable_cpow {r : ℂ} (h : 0 ≤ r.re ∨ (0 : ℝ) ∉ [[a, b]]) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) μ a b := by
  by_cases h2 : (0 : ℝ) ∉ [[a, b]]
  · -- Easy case #1: 0 ∉ [a, b] -- use continuity.
    refine' (ContinuousAt.continuousOn fun x hx => _).intervalIntegrable
    exact Complex.continuousAt_of_real_cpow_const _ _ (Or.inr <| ne_of_mem_of_not_mem hx h2)
  rw [eq_false h2, or_false_iff] at h 
  rcases lt_or_eq_of_le h with (h' | h')
  ·-- Easy case #2: 0 < re r -- again use continuity
    exact (Complex.continuous_of_real_cpow_const h').intervalIntegrable _ _
  -- Now the hard case: re r = 0 and 0 is in the interval.
  refine' (IntervalIntegrable.intervalIntegrable_norm_iff _).mp _
  · refine' (measurable_of_continuousOn_compl_singleton (0 : ℝ) _).AEStronglyMeasurable
    exact
      ContinuousAt.continuousOn fun x hx => Complex.continuousAt_of_real_cpow_const x r (Or.inr hx)
  -- reduce to case of integral over `[0, c]`
  suffices : ∀ c : ℝ, IntervalIntegrable (fun x : ℝ => ‖↑x ^ r‖) μ 0 c
  exact (this a).symm.trans (this b)
  intro c
  rcases le_or_lt 0 c with (hc | hc)
  · -- case `0 ≤ c`: integrand is identically 1
    have : IntervalIntegrable (fun x => 1 : ℝ → ℝ) μ 0 c := intervalIntegrable_const
    rw [intervalIntegrable_iff_integrable_Ioc_of_le hc] at this ⊢
    refine' integrable_on.congr_fun this (fun x hx => _) measurableSet_Ioc
    dsimp only
    rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hx.1, ← h', rpow_zero]
  · -- case `c < 0`: integrand is identically constant, *except* at `x = 0` if `r ≠ 0`.
    apply IntervalIntegrable.symm
    rw [intervalIntegrable_iff_integrable_Ioc_of_le hc.le]
    have : Ioc c 0 = Ioo c 0 ∪ {(0 : ℝ)} := by
      rw [← Ioo_union_Icc_eq_Ioc hc (le_refl 0), ← Icc_def]
      simp_rw [← le_antisymm_iff, set_of_eq_eq_singleton']
    rw [this, integrable_on_union, and_comm]; constructor
    · refine' integrable_on_singleton_iff.mpr (Or.inr _)
      exact
        is_finite_measure_on_compacts_of_is_locally_finite_measure.lt_top_of_is_compact
          isCompact_singleton
    · have : ∀ x : ℝ, x ∈ Ioo c 0 → ‖Complex.exp (↑π * Complex.I * r)‖ = ‖(x : ℂ) ^ r‖ := by
        intro x hx
        rw [Complex.of_real_cpow_of_nonpos hx.2.le, norm_mul, ← Complex.ofReal_neg,
          Complex.norm_eq_abs (_ ^ _), Complex.abs_cpow_eq_rpow_re_of_pos (neg_pos.mpr hx.2), ← h',
          rpow_zero, one_mul]
      refine' integrable_on.congr_fun _ this measurableSet_Ioo
      rw [integrable_on_const]
      refine' Or.inr ((measure_mono Set.Ioo_subset_Icc_self).trans_lt _)
      exact
        is_finite_measure_on_compacts_of_is_locally_finite_measure.lt_top_of_is_compact
          is_compact_Icc
#align interval_integral.interval_integrable_cpow intervalIntegral.intervalIntegrable_cpow

/-- See `interval_integrable_cpow` for a version applying to any locally finite measure, but with a
stronger hypothesis on `r`. -/
theorem intervalIntegrable_cpow' {r : ℂ} (h : -1 < r.re) :
    IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ r) volume a b := by
  suffices ∀ c : ℝ, IntervalIntegrable (fun x => (x : ℂ) ^ r) volume 0 c by
    exact IntervalIntegrable.trans (this a).symm (this b)
  have : ∀ c : ℝ, 0 ≤ c → IntervalIntegrable (fun x => (x : ℂ) ^ r) volume 0 c := by
    intro c hc
    rw [← IntervalIntegrable.intervalIntegrable_norm_iff]
    · rw [intervalIntegrable_iff]
      apply integrable_on.congr_fun
      · rw [← intervalIntegrable_iff]; exact intervalIntegral.intervalIntegrable_rpow' h
      · intro x hx
        rw [uIoc_of_le hc] at hx 
        dsimp only
        rw [Complex.norm_eq_abs, Complex.abs_cpow_eq_rpow_re_of_pos hx.1]
      · exact measurableSet_uIoc
    · refine' ContinuousOn.aestronglyMeasurable _ measurableSet_uIoc
      refine' ContinuousAt.continuousOn fun x hx => _
      rw [uIoc_of_le hc] at hx 
      refine' (continuousAt_cpow_const (Or.inl _)).comp complex.continuous_of_real.continuous_at
      rw [Complex.ofReal_re]
      exact hx.1
  intro c; rcases le_total 0 c with (hc | hc)
  · exact this c hc
  · rw [IntervalIntegrable.iff_comp_neg, neg_zero]
    have m := (this (-c) (by linarith)).const_mul (Complex.exp (π * Complex.I * r))
    rw [intervalIntegrable_iff, uIoc_of_le (by linarith : 0 ≤ -c)] at m ⊢
    refine' m.congr_fun (fun x hx => _) measurableSet_Ioc
    dsimp only
    have : -x ≤ 0 := by linarith [hx.1]
    rw [Complex.of_real_cpow_of_nonpos this, mul_comm]
    simp
#align interval_integral.interval_integrable_cpow' intervalIntegral.intervalIntegrable_cpow'

@[simp]
theorem intervalIntegrable_id : IntervalIntegrable (fun x => x) μ a b :=
  continuous_id.intervalIntegrable a b
#align interval_integral.interval_integrable_id intervalIntegral.intervalIntegrable_id

@[simp]
theorem intervalIntegrable_const : IntervalIntegrable (fun x => c) μ a b :=
  continuous_const.intervalIntegrable a b
#align interval_integral.interval_integrable_const intervalIntegral.intervalIntegrable_const

theorem intervalIntegrable_one_div (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0)
    (hf : ContinuousOn f [[a, b]]) : IntervalIntegrable (fun x => 1 / f x) μ a b :=
  (continuousOn_const.div hf h).intervalIntegrable
#align interval_integral.interval_integrable_one_div intervalIntegral.intervalIntegrable_one_div

@[simp]
theorem intervalIntegrable_inv (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0) (hf : ContinuousOn f [[a, b]]) :
    IntervalIntegrable (fun x => (f x)⁻¹) μ a b := by
  simpa only [one_div] using interval_integrable_one_div h hf
#align interval_integral.interval_integrable_inv intervalIntegral.intervalIntegrable_inv

@[simp]
theorem intervalIntegrable_exp : IntervalIntegrable exp μ a b :=
  continuous_exp.intervalIntegrable a b
#align interval_integral.interval_integrable_exp intervalIntegral.intervalIntegrable_exp

@[simp]
theorem IntervalIntegrable.log (hf : ContinuousOn f [[a, b]]) (h : ∀ x : ℝ, x ∈ [[a, b]] → f x ≠ 0) :
    IntervalIntegrable (fun x => log (f x)) μ a b :=
  (ContinuousOn.log hf h).intervalIntegrable
#align interval_integrable.log IntervalIntegrable.log

@[simp]
theorem intervalIntegrable_log (h : (0 : ℝ) ∉ [[a, b]]) : IntervalIntegrable log μ a b :=
  IntervalIntegrable.log continuousOn_id fun x hx => ne_of_mem_of_not_mem hx h
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
    IntervalIntegrable (fun x : ℝ => 1 / (1 + x ^ 2)) μ a b := by
  refine' (continuous_const.div _ fun x => _).intervalIntegrable a b
  · continuity
  · nlinarith
#align interval_integral.interval_integrable_one_div_one_add_sq intervalIntegral.intervalIntegrable_one_div_one_add_sq

@[simp]
theorem intervalIntegrable_inv_one_add_sq : IntervalIntegrable (fun x : ℝ => (1 + x ^ 2)⁻¹) μ a b :=
  by simpa only [one_div] using interval_integrable_one_div_one_add_sq
#align interval_integral.interval_integrable_inv_one_add_sq intervalIntegral.intervalIntegrable_inv_one_add_sq

/-! ### Integrals of the form `c * ∫ x in a..b, f (c * x + d)` -/


@[simp]
theorem mul_integral_comp_mul_right : (c * ∫ x in a..b, f (x * c)) = ∫ x in a * c..b * c, f x :=
  smul_integral_comp_mul_right f c
#align interval_integral.mul_integral_comp_mul_right intervalIntegral.mul_integral_comp_mul_right

@[simp]
theorem mul_integral_comp_mul_left : (c * ∫ x in a..b, f (c * x)) = ∫ x in c * a..c * b, f x :=
  smul_integral_comp_mul_left f c
#align interval_integral.mul_integral_comp_mul_left intervalIntegral.mul_integral_comp_mul_left

@[simp]
theorem inv_mul_integral_comp_div : (c⁻¹ * ∫ x in a..b, f (x / c)) = ∫ x in a / c..b / c, f x :=
  inv_smul_integral_comp_div f c
#align interval_integral.inv_mul_integral_comp_div intervalIntegral.inv_mul_integral_comp_div

@[simp]
theorem mul_integral_comp_mul_add :
    (c * ∫ x in a..b, f (c * x + d)) = ∫ x in c * a + d..c * b + d, f x :=
  smul_integral_comp_mul_add f c d
#align interval_integral.mul_integral_comp_mul_add intervalIntegral.mul_integral_comp_mul_add

@[simp]
theorem mul_integral_comp_add_mul :
    (c * ∫ x in a..b, f (d + c * x)) = ∫ x in d + c * a..d + c * b, f x :=
  smul_integral_comp_add_mul f c d
#align interval_integral.mul_integral_comp_add_mul intervalIntegral.mul_integral_comp_add_mul

@[simp]
theorem inv_mul_integral_comp_div_add :
    (c⁻¹ * ∫ x in a..b, f (x / c + d)) = ∫ x in a / c + d..b / c + d, f x :=
  inv_smul_integral_comp_div_add f c d
#align interval_integral.inv_mul_integral_comp_div_add intervalIntegral.inv_mul_integral_comp_div_add

@[simp]
theorem inv_mul_integral_comp_add_div :
    (c⁻¹ * ∫ x in a..b, f (d + x / c)) = ∫ x in d + a / c..d + b / c, f x :=
  inv_smul_integral_comp_add_div f c d
#align interval_integral.inv_mul_integral_comp_add_div intervalIntegral.inv_mul_integral_comp_add_div

@[simp]
theorem mul_integral_comp_mul_sub :
    (c * ∫ x in a..b, f (c * x - d)) = ∫ x in c * a - d..c * b - d, f x :=
  smul_integral_comp_mul_sub f c d
#align interval_integral.mul_integral_comp_mul_sub intervalIntegral.mul_integral_comp_mul_sub

@[simp]
theorem mul_integral_comp_sub_mul :
    (c * ∫ x in a..b, f (d - c * x)) = ∫ x in d - c * b..d - c * a, f x :=
  smul_integral_comp_sub_mul f c d
#align interval_integral.mul_integral_comp_sub_mul intervalIntegral.mul_integral_comp_sub_mul

@[simp]
theorem inv_mul_integral_comp_div_sub :
    (c⁻¹ * ∫ x in a..b, f (x / c - d)) = ∫ x in a / c - d..b / c - d, f x :=
  inv_smul_integral_comp_div_sub f c d
#align interval_integral.inv_mul_integral_comp_div_sub intervalIntegral.inv_mul_integral_comp_div_sub

@[simp]
theorem inv_mul_integral_comp_sub_div :
    (c⁻¹ * ∫ x in a..b, f (d - x / c)) = ∫ x in d - b / c..d - a / c, f x :=
  inv_smul_integral_comp_sub_div f c d
#align interval_integral.inv_mul_integral_comp_sub_div intervalIntegral.inv_mul_integral_comp_sub_div

end intervalIntegral

open intervalIntegral

/-! ### Integrals of simple functions -/


theorem integral_cpow {r : ℂ} (h : -1 < r.re ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    (∫ x : ℝ in a..b, (x : ℂ) ^ r) = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  rw [sub_div]
  have hr : r + 1 ≠ 0 := by
    cases h
    · apply_fun Complex.re
      rw [Complex.add_re, Complex.one_re, Complex.zero_re, Ne.def, add_eq_zero_iff_eq_neg]
      exact h.ne'
    · rw [Ne.def, ← add_eq_zero_iff_eq_neg] at h ; exact h.1
  by_cases hab : (0 : ℝ) ∉ [[a, b]]
  · refine' integral_eq_sub_of_has_deriv_at (fun x hx => _) (interval_integrable_cpow <| Or.inr hab)
    refine' hasDerivAt_of_real_cpow (ne_of_mem_of_not_mem hx hab) _
    contrapose! hr; rwa [add_eq_zero_iff_eq_neg]
  replace h : -1 < r.re; · tauto
  suffices ∀ c : ℝ, (∫ x : ℝ in 0 ..c, (x : ℂ) ^ r) = c ^ (r + 1) / (r + 1) - 0 ^ (r + 1) / (r + 1)
    by
    rw [←
      integral_add_adjacent_intervals (@interval_integrable_cpow' a 0 r h)
        (@interval_integrable_cpow' 0 b r h),
      integral_symm, this a, this b, Complex.zero_cpow hr]
    ring
  intro c
  apply integral_eq_sub_of_has_deriv_right
  · refine' ((Complex.continuous_of_real_cpow_const _).div_const _).ContinuousOn
    rwa [Complex.add_re, Complex.one_re, ← neg_lt_iff_pos_add]
  · refine' fun x hx => (hasDerivAt_of_real_cpow _ _).HasDerivWithinAt
    · rcases le_total c 0 with (hc | hc)
      · rw [max_eq_left hc] at hx ; exact hx.2.Ne; · rw [min_eq_left hc] at hx ; exact hx.1.ne'
    · contrapose! hr; rw [hr]; ring
  · exact interval_integrable_cpow' h
#align integral_cpow integral_cpow

theorem integral_rpow {r : ℝ} (h : -1 < r ∨ r ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    (∫ x in a..b, x ^ r) = (b ^ (r + 1) - a ^ (r + 1)) / (r + 1) := by
  have h' : -1 < (r : ℂ).re ∨ (r : ℂ) ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]] := by
    cases h
    · left; rwa [Complex.ofReal_re]
    · right; rwa [← Complex.ofReal_one, ← Complex.ofReal_neg, Ne.def, Complex.ofReal_inj]
  have :
    (∫ x in a..b, (x : ℂ) ^ (r : ℂ)) = ((b : ℂ) ^ (r + 1 : ℂ) - (a : ℂ) ^ (r + 1 : ℂ)) / (r + 1) :=
    integral_cpow h'
  apply_fun Complex.re at this ; convert this
  · simp_rw [interval_integral_eq_integral_uIoc, Complex.real_smul, Complex.ofReal_mul_re]
    · change Complex.re with IsROrC.re
      rw [← integral_re]; rfl
      refine' interval_integrable_iff.mp _
      cases h'
      · exact interval_integrable_cpow' h'; · exact interval_integrable_cpow (Or.inr h'.2)
  · rw [(by push_cast : (r : ℂ) + 1 = ((r + 1 : ℝ) : ℂ))]
    simp_rw [div_eq_inv_mul, ← Complex.ofReal_inv, Complex.ofReal_mul_re, Complex.sub_re]
    rfl
#align integral_rpow integral_rpow

theorem integral_zpow {n : ℤ} (h : 0 ≤ n ∨ n ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]) :
    (∫ x in a..b, x ^ n) = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  replace h : -1 < (n : ℝ) ∨ (n : ℝ) ≠ -1 ∧ (0 : ℝ) ∉ [[a, b]]; · exact_mod_cast h
  exact_mod_cast integral_rpow h
#align integral_zpow integral_zpow

@[simp]
theorem integral_pow : (∫ x in a..b, x ^ n) = (b ^ (n + 1) - a ^ (n + 1)) / (n + 1) := by
  simpa only [← Int.ofNat_succ, zpow_ofNat] using integral_zpow (Or.inl (Int.coe_nat_nonneg n))
#align integral_pow integral_pow

/-- Integral of `|x - a| ^ n` over `Ι a b`. This integral appears in the proof of the
Picard-Lindelöf/Cauchy-Lipschitz theorem. -/
theorem integral_pow_abs_sub_uIoc : (∫ x in Ι a b, |x - a| ^ n) = |b - a| ^ (n + 1) / (n + 1) := by
  cases' le_or_lt a b with hab hab
  ·
    calc
      (∫ x in Ι a b, |x - a| ^ n) = ∫ x in a..b, |x - a| ^ n := by
        rw [uIoc_of_le hab, ← integral_of_le hab]
      _ = ∫ x in 0 ..b - a, x ^ n := by
        simp only [integral_comp_sub_right fun x => |x| ^ n, sub_self]
        refine' integral_congr fun x hx => congr_arg₂ Pow.pow (abs_of_nonneg <| _) rfl
        rw [uIcc_of_le (sub_nonneg.2 hab)] at hx 
        exact hx.1
      _ = |b - a| ^ (n + 1) / (n + 1) := by simp [abs_of_nonneg (sub_nonneg.2 hab)]
      
  ·
    calc
      (∫ x in Ι a b, |x - a| ^ n) = ∫ x in b..a, |x - a| ^ n := by
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
theorem integral_id : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 := by simpa using integral_pow 1
#align integral_id integral_id

@[simp]
theorem integral_one : (∫ x in a..b, (1 : ℝ)) = b - a := by
  simp only [mul_one, smul_eq_mul, integral_const]
#align integral_one integral_one

theorem integral_const_on_unit_interval : (∫ x in a..a + 1, b) = b := by simp
#align integral_const_on_unit_interval integral_const_on_unit_interval

@[simp]
theorem integral_inv (h : (0 : ℝ) ∉ [[a, b]]) : (∫ x in a..b, x⁻¹) = log (b / a) := by
  have h' := fun x hx => ne_of_mem_of_not_mem hx h
  rw [integral_deriv_eq_sub' _ deriv_log' (fun x hx => differentiable_at_log (h' x hx))
      (continuous_on_inv₀.mono <| subset_compl_singleton_iff.mpr h),
    log_div (h' b right_mem_uIcc) (h' a left_mem_uIcc)]
#align integral_inv integral_inv

@[simp]
theorem integral_inv_of_pos (ha : 0 < a) (hb : 0 < b) : (∫ x in a..b, x⁻¹) = log (b / a) :=
  integral_inv <| not_mem_uIcc_of_lt ha hb
#align integral_inv_of_pos integral_inv_of_pos

@[simp]
theorem integral_inv_of_neg (ha : a < 0) (hb : b < 0) : (∫ x in a..b, x⁻¹) = log (b / a) :=
  integral_inv <| not_mem_uIcc_of_gt ha hb
#align integral_inv_of_neg integral_inv_of_neg

theorem integral_one_div (h : (0 : ℝ) ∉ [[a, b]]) : (∫ x : ℝ in a..b, 1 / x) = log (b / a) := by
  simp only [one_div, integral_inv h]
#align integral_one_div integral_one_div

theorem integral_one_div_of_pos (ha : 0 < a) (hb : 0 < b) :
    (∫ x : ℝ in a..b, 1 / x) = log (b / a) := by simp only [one_div, integral_inv_of_pos ha hb]
#align integral_one_div_of_pos integral_one_div_of_pos

theorem integral_one_div_of_neg (ha : a < 0) (hb : b < 0) :
    (∫ x : ℝ in a..b, 1 / x) = log (b / a) := by simp only [one_div, integral_inv_of_neg ha hb]
#align integral_one_div_of_neg integral_one_div_of_neg

@[simp]
theorem integral_exp : (∫ x in a..b, exp x) = exp b - exp a := by
  rw [integral_deriv_eq_sub'] <;> norm_num [continuousOn_exp]
#align integral_exp integral_exp

theorem integral_exp_mul_complex {c : ℂ} (hc : c ≠ 0) :
    (∫ x in a..b, Complex.exp (c * x)) = (Complex.exp (c * b) - Complex.exp (c * a)) / c := by
  have D : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (c * y) / c) (Complex.exp (c * x)) x := by
    intro x
    conv =>
      congr
      skip
      rw [← mul_div_cancel (Complex.exp (c * x)) hc]
    convert ((Complex.hasDerivAt_exp _).comp x _).div_const c using 1
    simpa only [mul_one] using ((hasDerivAt_id (x : ℂ)).const_mul _).comp_of_real
  rw [integral_deriv_eq_sub' _ (funext fun x => (D x).deriv) fun x hx => (D x).DifferentiableAt]
  · ring_nf
  · apply Continuous.continuousOn; continuity
#align integral_exp_mul_complex integral_exp_mul_complex

@[simp]
theorem integral_log (h : (0 : ℝ) ∉ [[a, b]]) :
    (∫ x in a..b, log x) = b * log b - a * log a - b + a := by
  obtain ⟨h', heq⟩ := fun x hx => ne_of_mem_of_not_mem hx h, fun x hx => mul_inv_cancel (h' x hx)
  convert
      integral_mul_deriv_eq_deriv_mul (fun x hx => has_deriv_at_log (h' x hx))
        (fun x hx => hasDerivAt_id x)
        (continuous_on_inv₀.mono <| subset_compl_singleton_iff.mpr h).intervalIntegrable
        continuous_on_const.interval_integrable using
      1 <;>
    simp [integral_congr HEq, mul_comm, ← sub_add]
#align integral_log integral_log

@[simp]
theorem integral_log_of_pos (ha : 0 < a) (hb : 0 < b) :
    (∫ x in a..b, log x) = b * log b - a * log a - b + a :=
  integral_log <| not_mem_uIcc_of_lt ha hb
#align integral_log_of_pos integral_log_of_pos

@[simp]
theorem integral_log_of_neg (ha : a < 0) (hb : b < 0) :
    (∫ x in a..b, log x) = b * log b - a * log a - b + a :=
  integral_log <| not_mem_uIcc_of_gt ha hb
#align integral_log_of_neg integral_log_of_neg

@[simp]
theorem integral_sin : (∫ x in a..b, sin x) = cos a - cos b := by
  rw [integral_deriv_eq_sub' fun x => -cos x] <;> norm_num [continuous_on_sin]
#align integral_sin integral_sin

@[simp]
theorem integral_cos : (∫ x in a..b, cos x) = sin b - sin a := by
  rw [integral_deriv_eq_sub'] <;> norm_num [continuous_on_cos]
#align integral_cos integral_cos

theorem integral_cos_mul_complex {z : ℂ} (hz : z ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Complex.cos (z * x)) = Complex.sin (z * b) / z - Complex.sin (z * a) / z := by
  apply integral_eq_sub_of_has_deriv_at
  swap
  · apply Continuous.intervalIntegrable
    exact complex.continuous_cos.comp (continuous_const.mul Complex.continuous_ofReal)
  intro x hx
  have a := Complex.hasDerivAt_sin (↑x * z)
  have b : HasDerivAt (fun y => y * z : ℂ → ℂ) z ↑x := hasDerivAt_mul_const _
  have c : HasDerivAt (fun y : ℂ => Complex.sin (y * z)) _ ↑x := HasDerivAt.comp x a b
  convert HasDerivAt.comp_of_real (c.div_const z)
  · simp_rw [mul_comm]
  · rw [mul_div_cancel _ hz, mul_comm]
#align integral_cos_mul_complex integral_cos_mul_complex

theorem integral_cos_sq_sub_sin_sq :
    (∫ x in a..b, cos x ^ 2 - sin x ^ 2) = sin b * cos b - sin a * cos a := by
  simpa only [sq, sub_eq_add_neg, neg_mul_eq_mul_neg] using
    integral_deriv_mul_eq_sub (fun x hx => has_deriv_at_sin x) (fun x hx => has_deriv_at_cos x)
      continuous_on_cos.interval_integrable continuous_on_sin.neg.interval_integrable
#align integral_cos_sq_sub_sin_sq integral_cos_sq_sub_sin_sq

@[simp]
theorem integral_inv_one_add_sq : (∫ x : ℝ in a..b, (1 + x ^ 2)⁻¹) = arctan b - arctan a := by
  simp only [← one_div]
  refine' integral_deriv_eq_sub' _ _ _ (continuous_const.div _ fun x => _).ContinuousOn
  · norm_num
  · norm_num
  · continuity
  · nlinarith
#align integral_inv_one_add_sq integral_inv_one_add_sq

theorem integral_one_div_one_add_sq : (∫ x : ℝ in a..b, 1 / (1 + x ^ 2)) = arctan b - arctan a := by
  simp only [one_div, integral_inv_one_add_sq]
#align integral_one_div_one_add_sq integral_one_div_one_add_sq

section RpowCpow

open Complex

theorem integral_mul_cpow_one_add_sq {t : ℂ} (ht : t ≠ -1) :
    (∫ x : ℝ in a..b, (x : ℂ) * (1 + x ^ 2) ^ t) =
      (1 + b ^ 2) ^ (t + 1) / (2 * (t + 1)) - (1 + a ^ 2) ^ (t + 1) / (2 * (t + 1)) := by
  have : t + 1 ≠ 0 := by contrapose! ht; rwa [add_eq_zero_iff_eq_neg] at ht 
  apply integral_eq_sub_of_has_deriv_at
  · intro x hx
    have f : HasDerivAt (fun y : ℂ => 1 + y ^ 2) (2 * x) x := by
      convert (hasDerivAt_pow 2 (x : ℂ)).const_add 1; · norm_cast; · simp
    have g :
      ∀ {z : ℂ}, 0 < z.re → HasDerivAt (fun z => z ^ (t + 1) / (2 * (t + 1))) (z ^ t / 2) z := by
      intro z hz
      have : z ≠ 0 := by contrapose! hz; rw [hz, zero_re]
      convert (HasDerivAt.cpow_const (hasDerivAt_id _) (Or.inl hz)).div_const (2 * (t + 1)) using 1
      field_simp
      ring
    convert (HasDerivAt.comp (↑x) (g _) f).comp_of_real using 1
    · field_simp; ring
    · rw [add_re, one_re, ← of_real_pow, of_real_re]
      exact add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg x)
  · apply Continuous.intervalIntegrable
    refine' continuous_of_real.mul _
    apply Continuous.cpow
    · exact continuous_const.add (continuous_of_real.pow 2)
    · exact continuous_const
    · intro a
      rw [add_re, one_re, ← of_real_pow, of_real_re]
      exact Or.inl (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg a))
#align integral_mul_cpow_one_add_sq integral_mul_cpow_one_add_sq

theorem integral_mul_rpow_one_add_sq {t : ℝ} (ht : t ≠ -1) :
    (∫ x : ℝ in a..b, x * (1 + x ^ 2) ^ t) =
      (1 + b ^ 2) ^ (t + 1) / (2 * (t + 1)) - (1 + a ^ 2) ^ (t + 1) / (2 * (t + 1)) := by
  have : ∀ x s : ℝ, (((1 + x ^ 2) ^ s : ℝ) : ℂ) = (1 + (x : ℂ) ^ 2) ^ ↑s := by
    intro x s
    rw [of_real_cpow, of_real_add, of_real_pow, of_real_one]
    exact add_nonneg zero_le_one (sq_nonneg x)
  rw [← of_real_inj]
  convert integral_mul_cpow_one_add_sq (_ : (t : ℂ) ≠ -1)
  · rw [← intervalIntegral.integral_ofReal]
    congr with x : 1
    rw [of_real_mul, this x t]
  · simp_rw [of_real_sub, of_real_div, this a (t + 1), this b (t + 1)]
    push_cast
  · rw [← of_real_one, ← of_real_neg, Ne.def, of_real_inj]
    exact ht
#align integral_mul_rpow_one_add_sq integral_mul_rpow_one_add_sq

end RpowCpow

/-! ### Integral of `sin x ^ n` -/


theorem integral_sin_pow_aux :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b + (n + 1) * ∫ x in a..b, sin x ^ n) -
        (n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
  let C := sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b
  have h : ∀ α β γ : ℝ, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : ∀ x ∈ _, HasDerivAt (fun y => sin y ^ (n + 1)) ((n + 1 : ℕ) * cos x * sin x ^ n) x :=
    fun x hx => by simpa only [mul_right_comm] using (has_deriv_at_sin x).pow (n + 1)
  have hv : ∀ x ∈ [[a, b]], HasDerivAt (-cos) (sin x) x := fun x hx => by
    simpa only [neg_neg] using (has_deriv_at_cos x).neg
  have H := integral_mul_deriv_eq_deriv_mul hu hv _ _
  calc
    (∫ x in a..b, sin x ^ (n + 2)) = ∫ x in a..b, sin x ^ (n + 1) * sin x := by
      simp only [pow_succ']
    _ = C + (n + 1) * ∫ x in a..b, cos x ^ 2 * sin x ^ n := by simp [H, h, sq]
    _ = C + (n + 1) * ∫ x in a..b, sin x ^ n - sin x ^ (n + 2) := by
      simp [cos_sq', sub_mul, ← pow_add, add_comm]
    _ = (C + (n + 1) * ∫ x in a..b, sin x ^ n) - (n + 1) * ∫ x in a..b, sin x ^ (n + 2) := by
      rw [integral_sub, mul_sub, add_sub_assoc] <;> apply Continuous.intervalIntegrable <;>
        continuity
    
  all_goals apply Continuous.intervalIntegrable; continuity
#align integral_sin_pow_aux integral_sin_pow_aux

/-- The reduction formula for the integral of `sin x ^ n` for any natural `n ≥ 2`. -/
theorem integral_sin_pow :
    (∫ x in a..b, sin x ^ (n + 2)) =
      (sin a ^ (n + 1) * cos a - sin b ^ (n + 1) * cos b) / (n + 2) +
        (n + 1) / (n + 2) * ∫ x in a..b, sin x ^ n := by
  have : (n : ℝ) + 2 ≠ 0 := by exact_mod_cast succ_ne_zero n.succ
  field_simp
  convert eq_sub_iff_add_eq.mp (integral_sin_pow_aux n)
  ring
#align integral_sin_pow integral_sin_pow

@[simp]
theorem integral_sin_sq : (∫ x in a..b, sin x ^ 2) = (sin a * cos a - sin b * cos b + b - a) / 2 :=
  by field_simp [integral_sin_pow, add_sub_assoc]
#align integral_sin_sq integral_sin_sq

theorem integral_sin_pow_odd :
    (∫ x in 0 ..π, sin x ^ (2 * n + 1)) = 2 * ∏ i in range n, (2 * i + 2) / (2 * i + 3) := by
  induction' n with k ih; · norm_num
  rw [prod_range_succ_comm, mul_left_comm, ← ih, mul_succ, integral_sin_pow]
  norm_cast
  simp [-cast_add, field_simps]
#align integral_sin_pow_odd integral_sin_pow_odd

theorem integral_sin_pow_even :
    (∫ x in 0 ..π, sin x ^ (2 * n)) = π * ∏ i in range n, (2 * i + 1) / (2 * i + 2) := by
  induction' n with k ih; · simp
  rw [prod_range_succ_comm, mul_left_comm, ← ih, mul_succ, integral_sin_pow]
  norm_cast
  simp [-cast_add, field_simps]
#align integral_sin_pow_even integral_sin_pow_even

theorem integral_sin_pow_pos : 0 < ∫ x in 0 ..π, sin x ^ n := by
  rcases even_or_odd' n with ⟨k, rfl | rfl⟩ <;>
          simp only [integral_sin_pow_even, integral_sin_pow_odd] <;>
        refine' mul_pos (by norm_num [pi_pos]) (prod_pos fun n hn => div_pos _ _) <;>
      norm_cast <;>
    linarith
#align integral_sin_pow_pos integral_sin_pow_pos

theorem integral_sin_pow_succ_le : (∫ x in 0 ..π, sin x ^ (n + 1)) ≤ ∫ x in 0 ..π, sin x ^ n := by
  let H x h := pow_le_pow_of_le_one (sin_nonneg_of_mem_Icc h) (sin_le_one x) (n.le_add_right 1)
  refine' integral_mono_on pi_pos.le _ _ H <;> exact (continuous_sin.pow _).intervalIntegrable 0 π
#align integral_sin_pow_succ_le integral_sin_pow_succ_le

theorem integral_sin_pow_antitone : Antitone fun n : ℕ => ∫ x in 0 ..π, sin x ^ n :=
  antitone_nat_of_succ_le integral_sin_pow_succ_le
#align integral_sin_pow_antitone integral_sin_pow_antitone

/-! ### Integral of `cos x ^ n` -/


theorem integral_cos_pow_aux :
    (∫ x in a..b, cos x ^ (n + 2)) =
      (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a + (n + 1) * ∫ x in a..b, cos x ^ n) -
        (n + 1) * ∫ x in a..b, cos x ^ (n + 2) := by
  let C := cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a
  have h : ∀ α β γ : ℝ, β * α * γ * α = β * (α * α * γ) := fun α β γ => by ring
  have hu : ∀ x ∈ _, HasDerivAt (fun y => cos y ^ (n + 1)) (-(n + 1 : ℕ) * sin x * cos x ^ n) x :=
    fun x hx => by
    simpa only [mul_right_comm, neg_mul, mul_neg] using (has_deriv_at_cos x).pow (n + 1)
  have hv : ∀ x ∈ [[a, b]], HasDerivAt sin (cos x) x := fun x hx => has_deriv_at_sin x
  have H := integral_mul_deriv_eq_deriv_mul hu hv _ _
  calc
    (∫ x in a..b, cos x ^ (n + 2)) = ∫ x in a..b, cos x ^ (n + 1) * cos x := by
      simp only [pow_succ']
    _ = C + (n + 1) * ∫ x in a..b, sin x ^ 2 * cos x ^ n := by simp [H, h, sq, -neg_add_rev]
    _ = C + (n + 1) * ∫ x in a..b, cos x ^ n - cos x ^ (n + 2) := by
      simp [sin_sq, sub_mul, ← pow_add, add_comm]
    _ = (C + (n + 1) * ∫ x in a..b, cos x ^ n) - (n + 1) * ∫ x in a..b, cos x ^ (n + 2) := by
      rw [integral_sub, mul_sub, add_sub_assoc] <;> apply Continuous.intervalIntegrable <;>
        continuity
    
  all_goals apply Continuous.intervalIntegrable; continuity
#align integral_cos_pow_aux integral_cos_pow_aux

/-- The reduction formula for the integral of `cos x ^ n` for any natural `n ≥ 2`. -/
theorem integral_cos_pow :
    (∫ x in a..b, cos x ^ (n + 2)) =
      (cos b ^ (n + 1) * sin b - cos a ^ (n + 1) * sin a) / (n + 2) +
        (n + 1) / (n + 2) * ∫ x in a..b, cos x ^ n := by
  have : (n : ℝ) + 2 ≠ 0 := by exact_mod_cast succ_ne_zero n.succ
  field_simp
  convert eq_sub_iff_add_eq.mp (integral_cos_pow_aux n)
  ring
#align integral_cos_pow integral_cos_pow

@[simp]
theorem integral_cos_sq : (∫ x in a..b, cos x ^ 2) = (cos b * sin b - cos a * sin a + b - a) / 2 :=
  by field_simp [integral_cos_pow, add_sub_assoc]
#align integral_cos_sq integral_cos_sq

/-! ### Integral of `sin x ^ m * cos x ^ n` -/


/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `n` is odd. -/
theorem integral_sin_pow_mul_cos_pow_odd (m n : ℕ) :
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) = ∫ u in sin a..sin b, u ^ m * (1 - u ^ 2) ^ n :=
  have hc : Continuous fun u : ℝ => u ^ m * (1 - u ^ 2) ^ n := by continuity
  calc
    (∫ x in a..b, sin x ^ m * cos x ^ (2 * n + 1)) =
        ∫ x in a..b, sin x ^ m * (1 - sin x ^ 2) ^ n * cos x :=
      by simp only [pow_succ', ← mul_assoc, pow_mul, cos_sq']
    _ = ∫ u in sin a..sin b, u ^ m * (1 - u ^ 2) ^ n :=
      integral_comp_mul_deriv (fun x hx => hasDerivAt_sin x) continuousOn_cos hc
    
#align integral_sin_pow_mul_cos_pow_odd integral_sin_pow_mul_cos_pow_odd

/-- The integral of `sin x * cos x`, given in terms of sin².
  See `integral_sin_mul_cos₂` below for the integral given in terms of cos². -/
@[simp]
theorem integral_sin_mul_cos₁ : (∫ x in a..b, sin x * cos x) = (sin b ^ 2 - sin a ^ 2) / 2 := by
  simpa using integral_sin_pow_mul_cos_pow_odd 1 0
#align integral_sin_mul_cos₁ integral_sin_mul_cos₁

@[simp]
theorem integral_sin_sq_mul_cos : (∫ x in a..b, sin x ^ 2 * cos x) = (sin b ^ 3 - sin a ^ 3) / 3 :=
  by simpa using integral_sin_pow_mul_cos_pow_odd 2 0
#align integral_sin_sq_mul_cos integral_sin_sq_mul_cos

@[simp]
theorem integral_cos_pow_three :
    (∫ x in a..b, cos x ^ 3) = sin b - sin a - (sin b ^ 3 - sin a ^ 3) / 3 := by
  simpa using integral_sin_pow_mul_cos_pow_odd 0 1
#align integral_cos_pow_three integral_cos_pow_three

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` is odd. -/
theorem integral_sin_pow_odd_mul_cos_pow (m n : ℕ) :
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) = ∫ u in cos b..cos a, u ^ n * (1 - u ^ 2) ^ m :=
  have hc : Continuous fun u : ℝ => u ^ n * (1 - u ^ 2) ^ m := by continuity
  calc
    (∫ x in a..b, sin x ^ (2 * m + 1) * cos x ^ n) =
        -∫ x in b..a, sin x ^ (2 * m + 1) * cos x ^ n :=
      by rw [integral_symm]
    _ = ∫ x in b..a, (1 - cos x ^ 2) ^ m * -sin x * cos x ^ n := by
      simp [pow_succ', pow_mul, sin_sq]
    _ = ∫ x in b..a, cos x ^ n * (1 - cos x ^ 2) ^ m * -sin x := by congr; ext; ring
    _ = ∫ u in cos b..cos a, u ^ n * (1 - u ^ 2) ^ m :=
      integral_comp_mul_deriv (fun x hx => hasDerivAt_cos x) continuousOn_sin.neg hc
    
#align integral_sin_pow_odd_mul_cos_pow integral_sin_pow_odd_mul_cos_pow

/-- The integral of `sin x * cos x`, given in terms of cos².
See `integral_sin_mul_cos₁` above for the integral given in terms of sin². -/
theorem integral_sin_mul_cos₂ : (∫ x in a..b, sin x * cos x) = (cos a ^ 2 - cos b ^ 2) / 2 := by
  simpa using integral_sin_pow_odd_mul_cos_pow 0 1
#align integral_sin_mul_cos₂ integral_sin_mul_cos₂

@[simp]
theorem integral_sin_mul_cos_sq : (∫ x in a..b, sin x * cos x ^ 2) = (cos a ^ 3 - cos b ^ 3) / 3 :=
  by simpa using integral_sin_pow_odd_mul_cos_pow 0 2
#align integral_sin_mul_cos_sq integral_sin_mul_cos_sq

@[simp]
theorem integral_sin_pow_three :
    (∫ x in a..b, sin x ^ 3) = cos a - cos b - (cos a ^ 3 - cos b ^ 3) / 3 := by
  simpa using integral_sin_pow_odd_mul_cos_pow 1 0
#align integral_sin_pow_three integral_sin_pow_three

/-- Simplification of the integral of `sin x ^ m * cos x ^ n`, case `m` and `n` are both even. -/
theorem integral_sin_pow_even_mul_cos_pow_even (m n : ℕ) :
    (∫ x in a..b, sin x ^ (2 * m) * cos x ^ (2 * n)) =
      ∫ x in a..b, ((1 - cos (2 * x)) / 2) ^ m * ((1 + cos (2 * x)) / 2) ^ n :=
  by field_simp [pow_mul, sin_sq, cos_sq, ← sub_sub, (by ring : (2 : ℝ) - 1 = 1)]
#align integral_sin_pow_even_mul_cos_pow_even integral_sin_pow_even_mul_cos_pow_even

@[simp]
theorem integral_sin_sq_mul_cos_sq :
    (∫ x in a..b, sin x ^ 2 * cos x ^ 2) = (b - a) / 8 - (sin (4 * b) - sin (4 * a)) / 32 := by
  convert integral_sin_pow_even_mul_cos_pow_even 1 1 using 1
  have h1 : ∀ c : ℝ, (1 - c) / 2 * ((1 + c) / 2) = (1 - c ^ 2) / 4 := fun c => by ring
  have h2 : Continuous fun x => cos (2 * x) ^ 2 := by continuity
  have h3 : ∀ x, cos x * sin x = sin (2 * x) / 2 := by intro; rw [sin_two_mul]; ring
  have h4 : ∀ d : ℝ, 2 * (2 * d) = 4 * d := fun d => by ring
  simp [h1, h2.interval_integrable, integral_comp_mul_left fun x => cos x ^ 2, h3, h4]
  ring
#align integral_sin_sq_mul_cos_sq integral_sin_sq_mul_cos_sq

