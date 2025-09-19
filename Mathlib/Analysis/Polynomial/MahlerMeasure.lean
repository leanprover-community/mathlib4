/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/

import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.MeasureTheory.Integral.CircleAverage

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

end Polynomial
