/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.SimpleRing.Principal

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
-/

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

variable {p} in
theorem logMahlerMeasure_eq_log_MahlerMeasure : p.logMahlerMeasure = log p.mahlerMeasure := by
  rw [mahlerMeasure]
  split_ifs <;> simp_all [logMahlerMeasure_def, circleAverage_def]

@[simp]
theorem mahlerMeasure_zero : (0 : ℂ[X]).mahlerMeasure = 0 := by simp [mahlerMeasure]

@[simp]
theorem mahlerMeasure_one : (1 : ℂ[X]).mahlerMeasure = 1 := by simp [mahlerMeasure]

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

theorem logMahlerMeasure_mul_eq_add_logMahelerMeasure {p q : ℂ[X]} (hpq : p * q ≠ 0) :
    (p * q).logMahlerMeasure = p.logMahlerMeasure + q.logMahlerMeasure := by
  simp_all [logMahlerMeasure_eq_log_MahlerMeasure, mahlerMeasure_mul, log_mul]


theorem logMahlerMeasure_C_mul {a : ℂ} (ha : a ≠ 0) {p : ℂ[X]} (hp : p ≠ 0) :
    (C a * p).logMahlerMeasure = log ‖a‖ + p.logMahlerMeasure := by
  rw [logMahlerMeasure_mul_eq_add_logMahelerMeasure (by simp [ha, hp]), logMahlerMeasure_const]

open MeromorphicOn Metric in
/-- The logarithmic Mahler measure of `X - C z` is the `log⁺` of the absolute value of `z`. -/
@[simp]
theorem logMahlerMeasure_X_sub_C (z : ℂ) : (X - C z).logMahlerMeasure = log⁺ ‖z‖ := by
  by_cases hz₀ : z = 0
  · simp [hz₀, posLog_def]
  have hmeroOn (U : Set ℂ) : MeromorphicOn (fun x ↦ x - z) U := MeromorphicOn.id.sub <| const z
  have hmeroAt (u : ℂ) : MeromorphicAt (fun x ↦ x - z) u := hmeroOn (Eq u) u rfl
  have hmeroBall : MeromorphicOn (fun x ↦ x - z) (closedBall 0 |1|) := hmeroOn (closedBall 0 |1|)
  have : MeromorphicOn (fun x ↦ (X - C z).eval x) (closedBall 0 |1|) :=
    (analyticOnNhd_id.aeval_polynomial (X - C z)).meromorphicOn
  rw [logMahlerMeasure_def, circleAverage_log_norm zero_ne_one.symm this]
  --get rid of the `meromorphicTrailingCoeffAt`
  have : meromorphicTrailingCoeffAt (fun x ↦ (X - C z).eval x) 0 = -z := by
    rw [(AnalyticAt.aeval_polynomial analyticAt_id (X - C z)).meromorphicTrailingCoeffAt_of_ne_zero
      (by simp [hz₀])]
    simp
  rw [this]
  simp only [eval_sub, eval_X, eval_C, zero_sub, norm_neg, one_mul, log_inv, mul_neg, log_one,
    mul_zero, add_zero]
  -- divisor computations
  let B := closedBall (0 : ℂ) |1|
  have hdiv0 {u : ℂ} (hu : u ≠ z) : divisor (fun x ↦ x - z) B u = 0 := by
    by_cases hu' : u ∈ B
    · rw [divisor_apply (hmeroOn B) hu', ← WithTop.untop₀_coe 0]
      congr
      rw [meromorphicOrderAt_eq_int_iff (hmeroAt u)]
      use fun x ↦ x - z
      simp only [zpow_zero, smul_eq_mul, one_mul, Filter.eventually_true, and_true]
      exact ⟨analyticAt_id.fun_sub analyticAt_const, sub_ne_zero_of_ne hu⟩
    · simp_all
  have hzdiv1 (h : z ∈ B) : (divisor (fun x ↦ x - z) B) z = 1 := by
      simp_all only [eval_sub, eval_X, eval_C, divisor_apply]
      rw [← WithTop.untop₀_coe 1]
      congr
      rw [meromorphicOrderAt_eq_int_iff (hmeroAt z)]
      use fun x ↦ 1
      simpa using analyticAt_const
  rw [← finsum_mem_support]
  --separate cases depending on whether z in in the open ball 0 |1| or not
  by_cases hzBall : z ∈ ball 0 |1|;
  · have : ‖z‖ < 1 := by rwa [mem_ball, dist_zero_right, abs_one] at hzBall
    have : ‖z‖ ≤ 1 := le_of_lt this
    have hzcb : z ∈ B := Set.mem_of_mem_of_subset hzBall ball_subset_closedBall
    have : (fun u ↦ -((divisor (fun x ↦ x - z) (closedBall 0 |1|) u) * log ‖u‖)).support = {z} := by
      rw [Function.support_eq_iff]
      constructor
      · simp only [ne_eq, neg_eq_zero, mul_eq_zero, Int.cast_eq_zero, log_eq_zero, norm_eq_zero]
        grind [norm_nonneg, ne_of_lt]
      · intro _ hu
        rw [Set.mem_singleton_iff] at hu
        rw [hdiv0 hu]
        simp
    simp only [this, Set.mem_singleton_iff, finsum_cond_eq_left]
    rw [hzdiv1 hzcb]
    grind [log_nonpos , norm_nonneg, posLog_def]
  · have h1lez : 1 ≤ ‖z‖ := by grind [mem_ball, dist_zero_right, abs_one]
    have : (fun u ↦ -((divisor (fun x ↦ x - z) (closedBall 0 |1|) u) * log ‖u‖)).support = ∅ := by
      rw [Function.support_eq_empty_iff]
      ext x
      simp only [Pi.ofNat_apply, neg_eq_zero, mul_eq_zero, Int.cast_eq_zero, log_eq_zero,
        norm_eq_zero, or_iff_not_imp_right, Classical.not_imp, and_imp]
      intro _ h _
      by_cases hx : x = z
      · rw [hx] at h ⊢
        apply Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
          (divisor (fun x ↦ x - z) (closedBall 0 |1|))
        grind [abs_one, mem_closedBall, dist_zero_right]
      · exact hdiv0 hx
    simp [this, posLog_eq_log_max_one <| norm_nonneg z, h1lez]

@[simp]
theorem logMahlerMeasure_X_add_C (z : ℂ) : (X + C z).logMahlerMeasure = log⁺ ‖z‖ := by
  simp [← sub_neg_eq_add, ← map_neg]

theorem logMahlerMeasure_C_mul_X_add_C {a : ℂ} (b : ℂ) (ha : a ≠ 0) :
    (C a * X + C b).logMahlerMeasure = log ‖a‖ + log⁺ ‖a⁻¹ * b‖ := by
  rw [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add, ← map_mul, ha],
    logMahlerMeasure_C_mul ha (X_add_C_ne_zero (a⁻¹ * b)), logMahlerMeasure_X_add_C]

theorem logMahlerMeasure_degree_eq_one {p : ℂ[X]} (h : p.degree = 1) : p.logMahlerMeasure =
    log ‖p.coeff 1‖ + log⁺ ‖(p.coeff 1)⁻¹ * p.coeff 0‖ := by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [logMahlerMeasure_C_mul_X_add_C _ (show p.coeff 1 ≠ 0 by exact coeff_ne_zero_of_eq_degree h)]

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

theorem mahlerMeasure_C_mul_X_add_C {a : ℂ} (b : ℂ) (ha : a ≠ 0) :
    (C a * X + C b).mahlerMeasure = ‖a‖ * max 1 ‖a⁻¹ * b‖ := by
  simp [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add, ← map_mul, ha],
    mahlerMeasure_mul, -map_mul]

theorem mahlerMeasure_degree_eq_one {p : ℂ[X]} (h : p.degree = 1) : p.mahlerMeasure =
    ‖p.coeff 1‖ * max 1 ‖(p.coeff 1)⁻¹ * p.coeff 0‖ := by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [mahlerMeasure_C_mul_X_add_C _ (show p.coeff 1 ≠ 0 by exact coeff_ne_zero_of_eq_degree h)]

/-- The logarithmic Mahler measure of a polynomial is the `log` of the absolute value of its leading
  coefficient plus the sum of the `log`s of the absolute values of its roots lying outside the unit
  disk. -/
theorem logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots (p : ℂ[X]) : p.logMahlerMeasure =
    log ‖p.leadingCoeff‖ + ((p.roots).map (fun a ↦ log⁺ ‖a‖)).sum := by
  by_cases hp : p = 0
  · simp [hp]
  have : ∀ x ∈ Multiset.map (fun x ↦ max 1 ‖x‖) p.roots, x ≠ 0 := by grind [Multiset.mem_map]
  nth_rw 1 [eq_prod_roots_of_splits_id (IsAlgClosed.splits p)]
  rw [logMahlerMeasure_mul_eq_add_logMahelerMeasure (by simp [hp, X_sub_C_ne_zero])]
  simp [posLog_eq_log_max_one, logMahlerMeasure_eq_log_MahlerMeasure,
    prod_mahlerMeasure_eq_mahlerMeasure_prod, log_multiset_prod this]

/-- The Mahler measure of a polynomial is the the absolute value of its leading coefficient times
  the product of the absolute values of its roots lying outside the unit disk. -/
theorem mahlerMeasure_eq_leadingCoeff_mul_prod_roots (p : ℂ[X]) : p.mahlerMeasure =
    ‖p.leadingCoeff‖ * ((p.roots).map (fun a ↦ max 1 ‖a‖)).prod := by
  by_cases hp : p = 0;
  · simp [hp]
  have := logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots p
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rw [exp_add, exp_log <| mahlerMeasure_pos_of_ne_zero hp,
    exp_log <|norm_pos_iff.mpr <| leadingCoeff_ne_zero.mpr hp] at this
  simp [this, exp_multiset_sum, posLog_eq_log_max_one, exp_log]

end Polynomial
