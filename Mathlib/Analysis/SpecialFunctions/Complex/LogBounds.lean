/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecificLimits.RCLike

/-!
# Estimates for the complex logarithm

We show that `log (1+z)` differs from its Taylor polynomial up to degree `n` by at most
`‖z‖^(n+1)/((n+1)*(1-‖z‖))` when `‖z‖ < 1`; see `Complex.norm_log_sub_logTaylor_le`.

To this end, we derive the representation of `log (1+z)` as the integral of `1/(1+tz)`
over the unit interval (`Complex.log_eq_integral`) and introduce notation
`Complex.logTaylor n` for the Taylor polynomial up to degree `n-1`.

## TODO

Refactor using general Taylor series theory, once this exists in Mathlib.
-/

@[expose] public section

namespace Complex

/-!
### Integral representation of the complex log
-/

set_option backward.isDefEq.respectTransparency false in
lemma continuousOn_one_add_mul_inv {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    ContinuousOn (fun t : ℝ ↦ (1 + t • z)⁻¹) (Set.Icc 0 1) :=
  ContinuousOn.inv₀ (by fun_prop)
    (fun _ ht ↦ slitPlane_ne_zero <| StarConvex.add_smul_mem starConvex_one_slitPlane hz ht.1 ht.2)

set_option backward.isDefEq.respectTransparency false in
open intervalIntegral in
/-- Represent `log (1 + z)` as an integral over the unit interval -/
lemma log_eq_integral {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    log (1 + z) = z * ∫ (t : ℝ) in (0 : ℝ)..1, (1 + t • z)⁻¹ := by
  convert (integral_unitInterval_deriv_eq_sub (continuousOn_one_add_mul_inv hz)
    (fun _ ht ↦ hasDerivAt_log <|
      StarConvex.add_smul_mem starConvex_one_slitPlane hz ht.1 ht.2)).symm using 1
  simp only [log_one, sub_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Represent `log (1 - z)⁻¹` as an integral over the unit interval -/
lemma log_inv_eq_integral {z : ℂ} (hz : 1 - z ∈ slitPlane) :
    log (1 - z)⁻¹ = z * ∫ (t : ℝ) in (0 : ℝ)..1, (1 - t • z)⁻¹ := by
  rw [sub_eq_add_neg 1 z] at hz ⊢
  rw [log_inv _ <| slitPlane_arg_ne_pi hz, neg_eq_iff_eq_neg, ← neg_mul]
  convert log_eq_integral hz using 5
  rw [sub_eq_add_neg, smul_neg]

/-!
### The Taylor polynomials of the logarithm
-/

/-- The `n`th Taylor polynomial of `log` at `1`, as a function `ℂ → ℂ` -/
noncomputable
def logTaylor (n : ℕ) : ℂ → ℂ := fun z ↦ ∑ j ∈ Finset.range n, (-1) ^ (j + 1) * z ^ j / j

lemma logTaylor_zero : logTaylor 0 = fun _ ↦ 0 := by
  funext
  simp only [logTaylor, Finset.range_zero,
    Finset.sum_empty]

lemma logTaylor_succ (n : ℕ) :
    logTaylor (n + 1) = logTaylor n + (fun z : ℂ ↦ (-1) ^ (n + 1) * z ^ n / n) := by
  funext
  simpa only [logTaylor] using Finset.sum_range_succ ..

lemma logTaylor_at_zero (n : ℕ) : logTaylor n 0 = 0 := by
  induction n with
  | zero => simp [logTaylor_zero]
  | succ n ih => simpa [logTaylor_succ, ih] using ne_or_eq n 0

lemma hasDerivAt_logTaylor (n : ℕ) (z : ℂ) :
    HasDerivAt (logTaylor (n + 1)) (∑ j ∈ Finset.range n, (-1) ^ j * z ^ j) z := by
  induction n with
  | zero => simp [logTaylor_succ, logTaylor_zero, Pi.add_def, hasDerivAt_const]
  | succ n ih =>
    rw [logTaylor_succ]
    simp only [Nat.cast_add, Nat.cast_one,
      Finset.sum_range_succ]
    refine HasDerivAt.add ih ?_
    simp only [mul_div_assoc]
    have : HasDerivAt (fun x : ℂ ↦ (x ^ (n + 1) / (n + 1))) (z ^ n) z := by
      simp_rw [div_eq_mul_inv]
      convert HasDerivAt.mul_const (hasDerivAt_pow (n + 1) z) (((n : ℂ) + 1)⁻¹) using 1
      simp [field]
    convert HasDerivAt.const_mul _ this using 2
    ring

/-!
### Bounds for the difference between log and its Taylor polynomials
-/

lemma hasDerivAt_log_sub_logTaylor (n : ℕ) {z : ℂ} (hz : 1 + z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ ↦ log (1 + z) - logTaylor (n + 1) z) ((-z) ^ n * (1 + z)⁻¹) z := by
  convert ((hasDerivAt_log hz).comp_const_add 1 z).sub (hasDerivAt_logTaylor n z) using 1
  have hz' : -z ≠ 1 := by
    intro H
    rw [neg_eq_iff_eq_neg] at H
    simp only [H, add_neg_cancel] at hz
    exact slitPlane_ne_zero hz rfl
  simp_rw [← mul_pow, neg_one_mul, geom_sum_eq hz', ← neg_add', div_neg, add_comm z]
  simp [field]

/-- Give a bound on `‖(1 + t * z)⁻¹‖` for `0 ≤ t ≤ 1` and `‖z‖ < 1`. -/
lemma norm_one_add_mul_inv_le {t : ℝ} (ht : t ∈ Set.Icc 0 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(1 + t * z)⁻¹‖ ≤ (1 - ‖z‖)⁻¹ := by
  rw [Set.mem_Icc] at ht
  rw [norm_inv]
  refine inv_anti₀ (by linarith) ?_
  calc 1 - ‖z‖
    _ ≤ 1 - t * ‖z‖ := by
      nlinarith [norm_nonneg z]
    _ = 1 - ‖t * z‖ := by
      rw [norm_mul, Complex.norm_of_nonneg ht.1]
    _ ≤ ‖1 + t * z‖ := by
      rw [← norm_neg (t * z), ← sub_neg_eq_add]
      convert norm_sub_norm_le 1 (-(t * z))
      exact norm_one.symm

lemma integrable_pow_mul_norm_one_add_mul_inv (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ n * ‖(1 + t * z)⁻¹‖) MeasureTheory.volume 0 1 := by
  have := continuousOn_one_add_mul_inv <| mem_slitPlane_of_norm_lt_one hz
  rw [← Set.uIcc_of_le zero_le_one] at this
  exact ContinuousOn.intervalIntegrable (by fun_prop)

set_option backward.isDefEq.respectTransparency false in
open intervalIntegral in
/-- The difference of `log (1+z)` and its `(n+1)`st Taylor polynomial can be bounded in
terms of `‖z‖`. -/
lemma norm_log_sub_logTaylor_le (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z) - logTaylor (n + 1) z‖ ≤ ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / (n + 1) := by
  have help : IntervalIntegrable (fun t : ℝ ↦ t ^ n * (1 - ‖z‖)⁻¹) MeasureTheory.volume 0 1 :=
    IntervalIntegrable.mul_const (Continuous.intervalIntegrable (by fun_prop) 0 1) (1 - ‖z‖)⁻¹
  let f (z : ℂ) : ℂ := log (1 + z) - logTaylor (n + 1) z
  let f' (z : ℂ) : ℂ := (-z) ^ n * (1 + z)⁻¹
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' (0 + t * z)) (0 + t * z) := by
    intro t ht
    rw [zero_add]
    exact hasDerivAt_log_sub_logTaylor n <|
      StarConvex.add_smul_mem starConvex_one_slitPlane (mem_slitPlane_of_norm_lt_one hz) ht.1 ht.2
  have hcont : ContinuousOn (fun t : ℝ ↦ f' (0 + t * z)) (Set.Icc 0 1) := by
    simp only [zero_add]
    exact (Continuous.continuousOn (by fun_prop)).mul <|
      continuousOn_one_add_mul_inv <| mem_slitPlane_of_norm_lt_one hz
  have H : f z = z * ∫ t in (0 : ℝ)..1, (-(t * z)) ^ n * (1 + t * z)⁻¹ := by
    convert (integral_unitInterval_deriv_eq_sub hcont hderiv).symm using 1
    · simp only [f, zero_add, add_zero, log_one, logTaylor_at_zero, sub_self, sub_zero]
    · simp only [f', real_smul, zero_add,
        smul_eq_mul]
  unfold f at H
  simp only [H, norm_mul]
  simp_rw [neg_pow (_ * z) n, mul_assoc, intervalIntegral.integral_const_mul, mul_pow,
    mul_comm _ (z ^ n), mul_assoc, intervalIntegral.integral_const_mul, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, one_mul, ← mul_assoc, ← pow_succ', mul_div_assoc]
  gcongr _ * ?_
  calc ‖∫ t in (0 : ℝ)..1, (t : ℂ) ^ n * (1 + t * z)⁻¹‖
    _ ≤ ∫ t in (0 : ℝ)..1, t ^ n * (1 - ‖z‖)⁻¹ := by
      refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one ?_ help
      filter_upwards with t ⟨ht₀, ht₁⟩
      rw [norm_mul, norm_pow, Complex.norm_of_nonneg ht₀.le]
      gcongr
      exact norm_one_add_mul_inv_le ⟨ht₀.le, ht₁⟩ hz
    _ = (1 - ‖z‖)⁻¹ / (n + 1) := by
      rw [intervalIntegral.integral_mul_const, mul_comm, integral_pow]
      simp [field]

/-- The difference `log (1+z) - z` is bounded by `‖z‖^2/(2*(1-‖z‖))` when `‖z‖ < 1`. -/
lemma norm_log_one_add_sub_self_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z) - z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  convert norm_log_sub_logTaylor_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_zero, sub_eq_add_neg]
  · norm_num

set_option linter.style.whitespace false in -- manual alignment is not recognised
open scoped Topology in
lemma log_sub_logTaylor_isBigO (n : ℕ) :
    (fun z ↦ log (1 + z) - logTaylor (n + 1) z) =O[𝓝 0] fun z ↦ z ^ (n + 1) := by
  rw [Asymptotics.isBigO_iff]
  use 2 / (n + 1)
  filter_upwards [
    eventually_norm_sub_lt 0 one_pos,
    eventually_norm_sub_lt 0 (show 0 < 1 / 2 by simp)] with z hz1 hz12
  rw [sub_zero] at hz1 hz12
  have : (1 - ‖z‖)⁻¹ ≤ 2 := by rw [inv_le_comm₀ (sub_pos_of_lt hz1) two_pos]; linarith
  apply (norm_log_sub_logTaylor_le n hz1).trans
  rw [mul_div_assoc, mul_comm, norm_pow]
  gcongr

open scoped Topology in
lemma log_sub_self_isBigO :
    (fun z ↦ log (1 + z) - z) =O[𝓝 0] fun z ↦ z ^ 2 := by
  convert log_sub_logTaylor_isBigO 1
  simp [logTaylor_succ, logTaylor_zero]

lemma norm_log_one_add_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 + z)‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 + ‖z‖ := by
  rw [← sub_add_cancel (log (1 + z)) z]
  exact norm_add_le_of_le (Complex.norm_log_one_add_sub_self_le hz) le_rfl

/-- For `‖z‖ ≤ 1/2`, the complex logarithm is bounded by `(3/2) * ‖z‖`. -/
lemma norm_log_one_add_half_le_self {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖log (1 + z)‖ ≤ (3 / 2) * ‖z‖ := by
  apply le_trans (norm_log_one_add_le (lt_of_le_of_lt hz one_half_lt_one))
  have hz3 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀]
    · linarith
    · linarith
  have hz4 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ / 2 * 2 / 2 := by
    gcongr
    · rw [inv_nonneg]
      linarith
    · rw [sq, div_eq_mul_one_div]
      gcongr
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel] at hz4
  linarith

/-- The difference of `log (1-z)⁻¹` and its `(n+1)`st Taylor polynomial can be bounded in
terms of `‖z‖`. -/
lemma norm_log_one_sub_inv_add_logTaylor_neg_le (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 - z)⁻¹ + logTaylor (n + 1) (-z)‖ ≤ ‖z‖ ^ (n + 1) * (1 - ‖z‖)⁻¹ / (n + 1) := by
  rw [sub_eq_add_neg,
    log_inv _ <| slitPlane_arg_ne_pi <| mem_slitPlane_of_norm_lt_one <| (norm_neg z).symm ▸ hz,
    ← sub_neg_eq_add, ← neg_sub', norm_neg]
  convert norm_log_sub_logTaylor_le n <| (norm_neg z).symm ▸ hz using 4 <;> rw [norm_neg]

/-- The difference `log (1-z)⁻¹ - z` is bounded by `‖z‖^2/(2*(1-‖z‖))` when `‖z‖ < 1`. -/
lemma norm_log_one_sub_inv_sub_self_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖log (1 - z)⁻¹ - z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
  convert norm_log_one_sub_inv_add_logTaylor_neg_le 1 hz using 2
  · simp [logTaylor_succ, logTaylor_zero, sub_eq_add_neg]
  · norm_num

set_option backward.isDefEq.respectTransparency false in
open Filter Asymptotics in
/-- The Taylor series of the complex logarithm at `1` converges to the logarithm in the
open unit disk. -/
lemma hasSum_taylorSeries_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ (-1) ^ (n + 1) * z ^ n / n) (log (1 + z)) := by
  refine (hasSum_iff_tendsto_nat_of_summable_norm ?_).mpr ?_
  · refine (summable_geometric_of_norm_lt_one hz).norm.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
    intro n
    simp only [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_natCast]
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    conv => enter [2]; rw [← div_one (‖z‖ ^ n)]
    gcongr
    norm_cast
  · rw [← tendsto_sub_nhds_zero_iff]
    conv => enter [1, x]; rw [← div_one (_ - _), ← logTaylor]
    rw [← isLittleO_iff_tendsto fun _ h ↦ (one_ne_zero h).elim]
    refine IsLittleO.trans_isBigO ?_ <| isBigO_const_one ℂ (1 : ℝ) atTop
    have H : (fun n ↦ logTaylor n z - log (1 + z)) =O[atTop] (fun n : ℕ ↦ ‖z‖ ^ n) := by
      have (n : ℕ) : ‖logTaylor n z - log (1 + z)‖
          ≤ (max ‖log (1 + z)‖ (1 - ‖z‖)⁻¹) * ‖(‖z‖ ^ n)‖ := by
        rw [norm_sub_rev, norm_pow, norm_norm]
        cases n with
        | zero => simp [logTaylor_zero]
        | succ n =>
            refine (norm_log_sub_logTaylor_le n hz).trans ?_
            rw [mul_comm, ← div_one ((max _ _) * _)]
            gcongr
            · exact le_max_right ..
            · linarith
      exact (isBigOWith_of_le' atTop this).isBigO
    refine IsBigO.trans_isLittleO H ?_
    convert isLittleO_pow_pow_of_lt_left (norm_nonneg z) hz
    exact (one_pow _).symm

/-- The series `∑ z^n/n` converges to `-log (1-z)` on the open unit disk. -/
lemma hasSum_taylorSeries_neg_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ ↦ z ^ n / n) (-log (1 - z)) := by
  conv => enter [1, n]; rw [← neg_neg (z ^ n / n)]
  refine HasSum.neg ?_
  convert hasSum_taylorSeries_log (z := -z) (norm_neg z ▸ hz) using 2 with n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  simp [field, pow_add, ← mul_pow]

end Complex

section Limits

/-! Limits of functions of the form `(1 + t/x + o(1/x)) ^ x` as `x → ∞`. -/

open Filter Asymptotics
open scoped Topology

namespace Complex

/-- The limit of `x * log (1 + g x)` as `(x : ℝ) → ∞` is `t`,
where `t : ℂ` is the limit of `x * g x`. -/
lemma tendsto_mul_log_one_add_of_tendsto {g : ℝ → ℂ} {t : ℂ}
    (hg : Tendsto (fun x ↦ x * g x) atTop (𝓝 t)) :
    Tendsto (fun x ↦ x * log (1 + g x)) atTop (𝓝 t) := by
  apply hg.congr_dist
  refine IsBigO.trans_tendsto ?_ tendsto_inv_atTop_zero.ofReal
  simp_rw [dist_comm (_ * g _), dist_eq, ← mul_sub, isBigO_norm_left]
  calc
    _ =O[atTop] fun x ↦ x * g x ^ 2 := by
      have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded hg.norm.isBoundedUnder_le
        (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
      exact (isBigO_refl _ _).mul (log_sub_self_isBigO.comp_tendsto hg0)
    _ =ᶠ[atTop] fun x ↦ (x * g x) ^ 2 * x⁻¹ := by
      filter_upwards [eventually_ne_atTop 0] with x hx0
      rw [ofReal_inv, eq_mul_inv_iff_mul_eq₀ (mod_cast hx0)]
      ring
    _ =O[atTop] _ := by
      simpa using isBigO_const_of_tendsto hg (one_ne_zero (α := ℂ))
        |>.pow 2 |>.mul (isBigO_refl _ _)

/-- The limit of `(1 + g x) ^ x` as `(x : ℝ) → ∞` is `exp t`,
where `t : ℂ` is the limit of `x * g x`. -/
lemma tendsto_one_add_cpow_exp_of_tendsto {g : ℝ → ℂ} {t : ℂ}
    (hg : Tendsto (fun x ↦ x * g x) atTop (𝓝 t)) :
    Tendsto (fun x ↦ (1 + g x) ^ (x : ℂ)) atTop (𝓝 (exp t)) := by
  apply ((continuous_exp.tendsto _).comp (tendsto_mul_log_one_add_of_tendsto hg)).congr'
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
  filter_upwards [hg0.eventually_ne (show 0 ≠ -1 by simp)] with x hg1
  dsimp
  rw [cpow_def_of_ne_zero, mul_comm]
  intro hg0
  rw [← add_eq_zero_iff_neg_eq.mp hg0] at hg1
  norm_num at hg1

/-- The limit of `(1 + t/x) ^ x` as `x → ∞` is `exp t` for `t : ℂ`. -/
lemma tendsto_one_add_div_cpow_exp (t : ℂ) :
    Tendsto (fun x : ℝ ↦ (1 + t / x) ^ (x : ℂ)) atTop (𝓝 (exp t)) := by
  apply tendsto_one_add_cpow_exp_of_tendsto
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_ne_atTop 0] with x hx0
  exact mul_div_cancel₀ t (mod_cast hx0)

/-- The limit of `n * log (1 + g n)` as `(n : ℝ) → ∞` is `t`,
where `t : ℂ` is the limit of `n * g n`. -/
lemma tendsto_nat_mul_log_one_add_of_tendsto {g : ℕ → ℂ} {t : ℂ}
    (hg : Tendsto (fun n ↦ n * g n) atTop (𝓝 t)) :
    Tendsto (fun n ↦ n * log (1 + g n)) atTop (𝓝 t) :=
  tendsto_mul_log_one_add_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
    |>.comp tendsto_natCast_atTop_atTop |>.congr (by simp)

/-- The limit of `(1 + g n) ^ n` as `(n : ℝ) → ∞` is `exp t`,
where `t : ℂ` is the limit of `n * g n`. -/
lemma tendsto_one_add_pow_exp_of_tendsto {g : ℕ → ℂ} {t : ℂ}
    (hg : Tendsto (fun n ↦ n * g n) atTop (𝓝 t)) :
    Tendsto (fun n ↦ (1 + g n) ^ n) atTop (𝓝 (exp t)) :=
  tendsto_one_add_cpow_exp_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg)
    |>.comp tendsto_natCast_atTop_atTop |>.congr (by simp)

/-- The limit of `(1 + t/n) ^ n` as `n → ∞` is `exp t` for `t : ℂ`. -/
lemma tendsto_one_add_div_pow_exp (t : ℂ) :
    Tendsto (fun n : ℕ ↦ (1 + t / n) ^ n) atTop (𝓝 (exp t)) :=
  tendsto_one_add_div_cpow_exp t |>.comp tendsto_natCast_atTop_atTop |>.congr (by simp)

end Complex

namespace Real

/-- The limit of `x * log (1 + g x)` as `(x : ℝ) → ∞` is `t`,
where `t : ℝ` is the limit of `x * g x`. -/
lemma tendsto_mul_log_one_add_of_tendsto {g : ℝ → ℝ} {t : ℝ}
    (hg : Tendsto (fun x ↦ x * g x) atTop (𝓝 t)) :
    Tendsto (fun x ↦ x * log (1 + g x)) atTop (𝓝 t) := by
  #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12179,
  `Real.cobounded_eq` was marked `@[simp]`, so didn't have to be passed explicitly here.
  Now the `simpNF` linter complains about it. -/
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (tendsto_id'.mpr (by simp [Real.cobounded_eq]))
  rw [← tendsto_ofReal_iff] at hg ⊢
  push_cast at hg ⊢
  apply (Complex.tendsto_mul_log_one_add_of_tendsto hg).congr'
  filter_upwards [hg0.eventually_const_le (show (-1 : ℝ) < 0 by simp)] with x hg1
  rw [Complex.ofReal_log (by linarith), Complex.ofReal_add, Complex.ofReal_one]

theorem tendsto_mul_log_one_add_div_atTop (t : ℝ) :
    Tendsto (fun x => x * log (1 + t / x)) atTop (𝓝 t) :=
  tendsto_mul_log_one_add_of_tendsto <|
    tendsto_const_nhds.congr' <|
      (EventuallyEq.div_mul_cancel_atTop tendsto_id).symm.trans <|
        .of_eq <| funext fun _ => mul_comm _ _

/-- The limit of `(1 + g x) ^ x` as `(x : ℝ) → ∞` is `exp t`,
where `t : ℝ` is the limit of `x * g x`. -/
lemma tendsto_one_add_rpow_exp_of_tendsto {g : ℝ → ℝ} {t : ℝ}
    (hg : Tendsto (fun x ↦ x * g x) atTop (𝓝 t)) :
    Tendsto (fun x ↦ (1 + g x) ^ x) atTop (𝓝 (exp t)) := by
  #adaptation_note /-- Prior to https://github.com/leanprover/lean4/pull/12179,
  `Real.cobounded_eq` was marked `@[simp]`, so didn't have to be passed explicitly here.
  Now the `simpNF` linter complains about it. -/
  have hg0 := tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
    hg.norm.isBoundedUnder_le (tendsto_id'.mpr (by simp [Real.cobounded_eq]))
  rw [← tendsto_ofReal_iff] at hg ⊢
  push_cast at hg ⊢
  apply (Complex.tendsto_one_add_cpow_exp_of_tendsto hg).congr'
  filter_upwards [hg0.eventually_const_le (show (-1 : ℝ) < 0 by simp)] with x hg1
  rw [Complex.ofReal_cpow (by linarith), Complex.ofReal_add, Complex.ofReal_one]

/-- The limit of `(1 + t/x) ^ x` as `x → ∞` is `exp t` for `t : ℝ`. -/
lemma tendsto_one_add_div_rpow_exp (t : ℝ) :
    Tendsto (fun x : ℝ ↦ (1 + t / x) ^ x) atTop (𝓝 (exp t)) := by
  apply tendsto_one_add_rpow_exp_of_tendsto
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [eventually_ne_atTop 0] with x hx0
  exact mul_div_cancel₀ t (mod_cast hx0)

/-- The limit of `n * log (1 + g n)` as `(n : ℝ) → ∞` is `t`,
where `t : ℝ` is the limit of `n * g n`. -/
lemma tendsto_nat_mul_log_one_add_of_tendsto {g : ℕ → ℝ} {t : ℝ}
    (hg : Tendsto (fun n ↦ n * g n) atTop (𝓝 t)) :
    Tendsto (fun n ↦ n * log (1 + g n)) atTop (𝓝 t) :=
  tendsto_mul_log_one_add_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg) |>.comp
    tendsto_natCast_atTop_atTop |>.congr (by simp)

/-- The limit of `(1 + g n) ^ n` as `(n : ℝ) → ∞` is `exp t`,
where `t : ℝ` is the limit of `n * g n`. -/
lemma tendsto_one_add_pow_exp_of_tendsto {g : ℕ → ℝ} {t : ℝ}
    (hg : Tendsto (fun n ↦ n * g n) atTop (𝓝 t)) :
    Tendsto (fun n ↦ (1 + g n) ^ n) atTop (𝓝 (exp t)) :=
  tendsto_one_add_rpow_exp_of_tendsto (tendsto_smul_comp_nat_floor_of_tendsto_mul hg) |>.comp
    tendsto_natCast_atTop_atTop |>.congr (by simp)

/-- The limit of `(1 + t/n) ^ n` as `n → ∞` is `exp t` for `t : ℝ`. -/
lemma tendsto_one_add_div_pow_exp (t : ℝ) :
    Tendsto (fun n : ℕ ↦ (1 + t / n) ^ n) atTop (𝓝 (exp t)) :=
  tendsto_one_add_div_rpow_exp t |>.comp tendsto_natCast_atTop_atTop |>.congr (by simp)

end Real

end Limits
