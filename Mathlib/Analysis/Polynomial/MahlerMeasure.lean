/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

/-!
# Mahler measure of complex polynomials

In this file we define the Mahler measure of a polynomial over `ℂ[X]` and prove some basic
properties.

## Main definitions

- `Polynomial.logMahlerMeasure p`: the logarithmic Mahler measure of a polynomial `p` defined as
  `(2 * π)⁻¹ * ∫ x ∈ (0, 2 * π), log ‖p (e ^ (i * x))‖`.
- `Polynomial.mahlerMeasure p`: the (exponential) Mahler measure of a polynomial `p`, which is equal
  to `e ^ p.logMahlerMeasure` if `p` is nonzero, and `0` otherwise.

## Main results

- `Polynomial.mahlerMeasure_mul`: the Mahler measure of the product of two polynomials is the
  product of their Mahler measures.
- `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`: the Mahler measure of a polynomial is the absolute
  value of its leading coefficient times the product of the absolute values of its roots lying
  outside the unit disk.
-/

@[expose] public section

namespace Polynomial

open Real

variable (p : ℂ[X])

/-- The logarithmic Mahler measure of a polynomial `p` defined as
`(2 * π)⁻¹ * ∫ x ∈ (0, 2 * π), log ‖p (e ^ (i * x))‖` -/
noncomputable def logMahlerMeasure : ℝ := circleAverage (fun x ↦ log ‖eval x p‖) 0 1

theorem logMahlerMeasure_def : p.logMahlerMeasure = circleAverage (fun x ↦ log ‖eval x p‖) 0 1 :=
  rfl

@[simp]
theorem logMahlerMeasure_zero : (0 : ℂ[X]).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]
theorem logMahlerMeasure_one : (1 : ℂ[X]).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure_def, circleAverage_def]

-- TODO rename logMahlerMeasure_C
@[simp]
theorem logMahlerMeasure_const (z : ℂ) : (C z).logMahlerMeasure = log ‖z‖ := by
  simp [logMahlerMeasure_def, circleAverage_def, mul_assoc]

@[simp]
theorem logMahlerMeasure_X : (X : ℂ[X]).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]
theorem logMahlerMeasure_monomial (n : ℕ) (z : ℂ) : (monomial n z).logMahlerMeasure = log ‖z‖ := by
  simp [logMahlerMeasure_def, circleAverage_def, mul_assoc]

/-- The Mahler measure of a polynomial `p` defined as `e ^ (logMahlerMeasure p)` if `p` is nonzero
and `0` otherwise -/
noncomputable def mahlerMeasure : ℝ := if p ≠ 0 then exp (p.logMahlerMeasure) else 0

variable {p} in
theorem mahlerMeasure_def_of_ne_zero (hp : p ≠ 0) : p.mahlerMeasure =
    exp ((2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖) := by
  simp [mahlerMeasure, hp, logMahlerMeasure_def, circleAverage_def]

-- TODO rename logMahlerMeasure_eq_log_mahlerMeasure
variable {p} in
theorem logMahlerMeasure_eq_log_MahlerMeasure : p.logMahlerMeasure = log p.mahlerMeasure := by
  rw [mahlerMeasure]
  split_ifs <;> simp_all [logMahlerMeasure_def, circleAverage_def]

@[simp]
theorem mahlerMeasure_zero : (0 : ℂ[X]).mahlerMeasure = 0 := by simp [mahlerMeasure]

@[simp]
theorem mahlerMeasure_one : (1 : ℂ[X]).mahlerMeasure = 1 := by simp [mahlerMeasure]

-- TODO rename mahlerMeasure_const
@[simp]
theorem mahlerMeasure_const (z : ℂ) : (C z).mahlerMeasure = ‖z‖ := by
  simp only [mahlerMeasure, ne_eq, map_eq_zero, logMahlerMeasure_const, ite_not]
  split_ifs with h
  · simp [h]
  · simp [h, exp_log]

theorem mahlerMeasure_nonneg : 0 ≤ p.mahlerMeasure := by
  by_cases hp : p = 0 <;> simp [hp, mahlerMeasure_def_of_ne_zero, exp_nonneg]

variable {p} in
theorem mahlerMeasure_pos_of_ne_zero (hp : p ≠ 0) : 0 < p.mahlerMeasure := by
  grind [exp_pos, mahlerMeasure_def_of_ne_zero]

@[simp]
theorem mahlerMeasure_eq_zero_iff : p.mahlerMeasure = 0 ↔ p = 0 := by
  refine ⟨?_, by simp_all [mahlerMeasure_zero]⟩
  contrapose
  exact fun h ↦ by simp [mahlerMeasure_def_of_ne_zero h]

lemma intervalIntegrable_mahlerMeasure :
    IntervalIntegrable (fun x ↦ log ‖p.eval (circleMap 0 1 x)‖) MeasureTheory.volume 0 (2 * π) := by
  rw [← circleIntegrable_def fun z ↦ log ‖p.eval z‖]
  exact circleIntegrable_log_norm_meromorphicOn
    <| (analyticOnNhd_id.aeval_polynomial p).meromorphicOn

/-! The Mahler measure of the product of two polynomials is the product of their Mahler measures -/
open intervalIntegral in
theorem mahlerMeasure_mul (p q : ℂ[X]) :
    (p * q).mahlerMeasure = p.mahlerMeasure * q.mahlerMeasure := by
  by_cases hpq : p * q = 0
  · simpa [hpq, mahlerMeasure_zero] using mul_eq_zero.mp hpq
  rw [mul_eq_zero, not_or] at hpq
  simp only [mahlerMeasure, ne_eq, mul_eq_zero, hpq, or_self, not_false_eq_true, ↓reduceIte,
    logMahlerMeasure, eval_mul, Complex.norm_mul, circleAverage_def, mul_inv_rev, smul_eq_mul]
  rw [← exp_add, ← left_distrib]
  congr
  rw [← integral_add p.intervalIntegrable_mahlerMeasure q.intervalIntegrable_mahlerMeasure]
  apply integral_congr_ae
  rw [MeasureTheory.ae_iff]
  apply Set.Finite.measure_zero _ MeasureTheory.volume
  simp only [_root_.not_imp]
  apply Set.Finite.of_finite_image (f := circleMap 0 1) _ <|
    (injOn_circleMap_of_abs_sub_le one_ne_zero (by simp [le_of_eq, pi_nonneg])).mono (fun _ h ↦ h.1)
  apply (p * q).roots.finite_toSet.subset
  rintro _ ⟨_, ⟨_, h⟩, _⟩
  contrapose h
  simp_all [log_mul]

@[simp]
theorem prod_mahlerMeasure_eq_mahlerMeasure_prod (s : Multiset ℂ[X]) :
    (s.prod).mahlerMeasure = (s.map (fun p ↦ p.mahlerMeasure)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [mahlerMeasure_mul, ih]

theorem logMahlerMeasure_mul_eq_add_logMahlerMeasure {p q : ℂ[X]} (hpq : p * q ≠ 0) :
    (p * q).logMahlerMeasure = p.logMahlerMeasure + q.logMahlerMeasure := by
  simp_all [logMahlerMeasure_eq_log_MahlerMeasure, mahlerMeasure_mul, log_mul]

@[deprecated (since := "2025-11-17")]
alias logMahlerMeasure_mul_eq_add_logMahelerMeasure := logMahlerMeasure_mul_eq_add_logMahlerMeasure

theorem logMahlerMeasure_C_mul {a : ℂ} (ha : a ≠ 0) {p : ℂ[X]} (hp : p ≠ 0) :
    (C a * p).logMahlerMeasure = log ‖a‖ + p.logMahlerMeasure := by
  rw [logMahlerMeasure_mul_eq_add_logMahlerMeasure (by simp [ha, hp]), logMahlerMeasure_const]

open MeromorphicOn Metric in
/-- The logarithmic Mahler measure of `X - C z` is the `log⁺` of the absolute value of `z`. -/
@[simp]
theorem logMahlerMeasure_X_sub_C (z : ℂ) : (X - C z).logMahlerMeasure = log⁺ ‖z‖ := by
  simp [logMahlerMeasure_def]

@[simp]
theorem logMahlerMeasure_X_add_C (z : ℂ) : (X + C z).logMahlerMeasure = log⁺ ‖z‖ := by
  simp [← sub_neg_eq_add, ← map_neg]

theorem logMahlerMeasure_C_mul_X_add_C {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    (C a * X + C b).logMahlerMeasure = log ‖a‖ + log⁺ ‖a⁻¹ * b‖ := by
  rw [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add, ← map_mul, ha],
    logMahlerMeasure_C_mul ha (X_add_C_ne_zero (a⁻¹ * b)), logMahlerMeasure_X_add_C]

theorem logMahlerMeasure_of_degree_eq_one {p : ℂ[X]} (h : p.degree = 1) : p.logMahlerMeasure =
    log ‖p.coeff 1‖ + log⁺ ‖(p.coeff 1)⁻¹ * p.coeff 0‖ := by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [logMahlerMeasure_C_mul_X_add_C (show p.coeff 1 ≠ 0 by exact coeff_ne_zero_of_eq_degree h)]

/-- The Mahler measure of `X - C z` equals `max 1 ‖z‖`. -/
@[simp]
theorem mahlerMeasure_X_sub_C (z : ℂ) : (X - C z).mahlerMeasure = max 1 ‖z‖ := by
  have := logMahlerMeasure_X_sub_C z
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rwa [posLog_eq_log_max_one (norm_nonneg z),
    exp_log (mahlerMeasure_pos_of_ne_zero <| X_sub_C_ne_zero z),
    exp_log (lt_of_lt_of_le zero_lt_one <| le_max_left 1 ‖z‖)] at this

@[simp]
theorem mahlerMeasure_X_add_C (z : ℂ) : (X + C z).mahlerMeasure = max 1 ‖z‖ := by
  simp [← sub_neg_eq_add, ← map_neg]

@[simp]
theorem mahlerMeasure_C_mul_X_add_C {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    (C a * X + C b).mahlerMeasure = max ‖a‖ ‖b‖ := by
  simp only [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add, ← map_mul, ha],
    mahlerMeasure_mul, mahlerMeasure_const, ← coe_nnnorm, mahlerMeasure_X_add_C]
  norm_cast
  simp [mul_max, ha]

theorem mahlerMeasure_of_degree_eq_one {p : ℂ[X]} (h : p.degree = 1) :
    p.mahlerMeasure = max ‖p.coeff 1‖ ‖p.coeff 0‖ := by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [mahlerMeasure_C_mul_X_add_C (show p.coeff 1 ≠ 0 by exact coeff_ne_zero_of_eq_degree h)]

/-- The logarithmic Mahler measure of a polynomial is the `log` of the absolute value of its leading
  coefficient plus the sum of the `log`s of the absolute values of its roots lying outside the unit
  disk. -/
theorem logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots (p : ℂ[X]) : p.logMahlerMeasure =
    log ‖p.leadingCoeff‖ + (p.roots.map (fun a ↦ log⁺ ‖a‖)).sum := by
  by_cases hp : p = 0
  · simp [hp]
  have : ∀ x ∈ Multiset.map (fun x ↦ max 1 ‖x‖) p.roots, x ≠ 0 := by grind [Multiset.mem_map]
  nth_rw 1 [(IsAlgClosed.splits p).eq_prod_roots]
  rw [logMahlerMeasure_mul_eq_add_logMahlerMeasure (by simp [hp, X_sub_C_ne_zero])]
  simp [posLog_eq_log_max_one, logMahlerMeasure_eq_log_MahlerMeasure,
    prod_mahlerMeasure_eq_mahlerMeasure_prod, log_multiset_prod this]

/-- The Mahler measure of a polynomial is the absolute value of its leading coefficient times
  the product of the absolute values of its roots lying outside the unit disk. -/
theorem mahlerMeasure_eq_leadingCoeff_mul_prod_roots (p : ℂ[X]) : p.mahlerMeasure =
    ‖p.leadingCoeff‖ * (p.roots.map (fun a ↦ max 1 ‖a‖)).prod := by
  by_cases hp : p = 0;
  · simp [hp]
  have := logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots p
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rw [exp_add, exp_log <| mahlerMeasure_pos_of_ne_zero hp,
    exp_log <|norm_pos_iff.mpr <| leadingCoeff_ne_zero.mpr hp] at this
  simp [this, exp_multiset_sum, posLog_eq_log_max_one, exp_log]

/-!
### Estimates for the Mahler measure
-/

lemma one_le_prod_max_one_norm_roots (p : ℂ[X]) : 1 ≤ (p.roots.map (fun a ↦ max 1 ‖a‖)).prod := by
  grind [Multiset.one_le_prod, Multiset.mem_map]

lemma leading_coeff_le_mahlerMeasure (p : ℂ[X]) : ‖p.leadingCoeff‖ ≤ p.mahlerMeasure := by
  rw [← mul_one ‖_‖, mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  gcongr
  exact one_le_prod_max_one_norm_roots p

lemma prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff {p : ℂ[X]}
    (hlc : 1 ≤ ‖p.leadingCoeff‖) : (p.roots.map (fun a ↦ max 1 ‖a‖)).prod ≤ p.mahlerMeasure := by
  rw [← one_mul (Multiset.prod _), mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  gcongr
  exact zero_le_one.trans <| one_le_prod_max_one_norm_roots p

open Filter MeasureTheory Set in
/-- The Mahler measure of a polynomial is bounded above by the sum of the norms of its coefficients.
-/
theorem mahlerMeasure_le_sum_norm_coeff (p : ℂ[X]) : p.mahlerMeasure ≤ p.sum fun _ a ↦ ‖a‖ := by
  by_cases hp : p = 0
  · simp [hp]
  have : 0 < p.sum fun _ a ↦ ‖a‖ :=
    Finset.sum_pos' (fun i _ ↦ norm_nonneg (p.coeff i)) ⟨p.natDegree, by simp [hp]⟩
  rw [show (p.sum fun _ a ↦ ‖a‖) = rexp (circleAverage (fun _ ↦ log (p.sum fun _ a ↦ ‖a‖)) 0 1)
    by simp [circleAverage_def, mul_assoc, exp_log this], mahlerMeasure_def_of_ne_zero hp,
    circleAverage_def, smul_eq_mul]
  gcongr
  apply intervalIntegral.integral_mono_ae_restrict (by positivity)
    p.intervalIntegrable_mahlerMeasure (by simp)
  rw [EventuallyLE, eventually_iff_exists_mem]
  use {x : ℝ | eval (circleMap 0 1 x) p ≠ 0}
  constructor
  · rw [mem_ae_iff, compl_def, Measure.restrict_apply' (by simp)]
    apply (Finite.of_diff _ <| finite_singleton (2 * π)).measure_zero
    simp only [ne_eq, mem_setOf_eq, Decidable.not_not, inter_diff_assoc, Icc_diff_right]
    rw [setOf_inter_eq_sep]
    apply Finite.of_finite_image (f := circleMap 0 1) ((Multiset.finite_toSet p.roots).subset _)
      <| fun _ h _ k l ↦ injOn_circleMap_of_abs_sub_le' one_ne_zero (by linarith) h.1 k.1 l
    simp [hp]
  · intro _ _
    gcongr
    rw [eval_eq_sum]
    apply norm_sum_le_of_le p.support
    simp

open Multiset in
theorem norm_coeff_le_choose_mul_mahlerMeasure (n : ℕ) (p : ℂ[X]) :
    ‖p.coeff n‖ ≤ (p.natDegree).choose n * p.mahlerMeasure := by
  by_cases hp : p = 0
  · simp [hp]
  rcases lt_or_ge p.natDegree n with hlt | hn
  · simp [coeff_eq_zero_of_natDegree_lt hlt, Nat.choose_eq_zero_of_lt hlt]
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, mul_left_comm,
    coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (IsAlgClosed.splits p)) hn, mul_assoc,
    norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    mul_le_mul_iff_right₀ (by simp [leadingCoeff_ne_zero.mpr hp]), esymm,
    Finset.sum_multiset_map_count]
  apply le_trans <| norm_sum_le _ _
  simp_rw [nsmul_eq_mul, norm_mul, _root_.norm_natCast]
  let S := powersetCard (p.natDegree - n) p.roots
  --to be used later in the calc block:
  have (x : Multiset ℂ) (hx : x ∈ S.toFinset) : ∏ x_1 ∈ x.toFinset, ‖x_1‖ ^ count x_1 x
      ≤ ∏ m ∈ p.roots.toFinset, max 1 ‖m‖ ^ count m p.roots := by
    rw [mem_toFinset, mem_powersetCard] at hx
    calc
    ∏ z ∈ x.toFinset, ‖z‖ ^ count z x
      ≤ ∏ z ∈ x.toFinset, (1 ⊔ ‖z‖) ^ count z x := by
      gcongr with a
      exact le_max_right 1 ‖a‖
    _ ≤ ∏ z ∈ p.roots.toFinset, (1 ⊔ ‖z‖) ^ count z x := by
      simp_rw [← coe_nnnorm]
      norm_cast
      exact Finset.prod_le_prod_of_subset_of_one_le' (toFinset_subset.mpr (subset_of_le hx.1))
        (fun a _ _ ↦ one_le_pow₀ (le_max_left 1 ‖a‖))
    _ ≤ ∏ z ∈ p.roots.toFinset, (1 ⊔ ‖z‖) ^ count z p.roots := by
      gcongr with a
      · exact le_max_left 1 ‖a‖
      · exact hx.1
  --final calc block:
  calc
  ∑ x ∈ S.toFinset, count x S * ‖x.prod‖
     ≤ ∑ x ∈ S.toFinset, count x S * ((p.roots).map (fun a ↦ max 1 ‖a‖)).prod := by
    gcongr with x hx
    rw [Finset.prod_multiset_map_count, Finset.prod_multiset_count, norm_prod]
    simp_rw [norm_pow]
    exact this x hx
  _  = p.natDegree.choose n * (p.roots.map (fun a ↦ 1 ⊔ ‖a‖)).prod := by
    rw [← Finset.sum_mul]
    congr
    norm_cast
    simp only [mem_powersetCard, mem_toFinset, imp_self, implies_true, sum_count_eq_card,
      card_powersetCard, S, ← Nat.choose_symm hn]
    congr
    exact splits_iff_card_roots.mp <| IsAlgClosed.splits p

end Polynomial
