/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Poisson distributions over ℕ

Define the Poisson measure over the natural numbers. For `r : ℝ≥0`, `poissonMeasure r` is the
measure which to `{n}` associates `exp (-r) * r ^ n / (n)!`.

## Main definition

* `poissonMeasure r`: a Poisson measure on `ℕ`, parametrized by its rate `r : ℝ≥0`.
-/

@[expose] public section

open MeasureTheory Real
open scoped NNReal Nat

namespace ProbabilityTheory

/-- The poisson measure with rate `r : ℝ≥0` as a measure over `ℕ`. -/
noncomputable
def poissonMeasure (r : ℝ≥0) : Measure ℕ :=
  Measure.sum (fun n ↦ ENNReal.ofReal (exp (-r) * r ^ n / (n)!) • (.dirac n))

lemma poissonMeasure_real_singleton (r : ℝ≥0) (n : ℕ) :
    (poissonMeasure r).real {n} = exp (-r) * r ^ n / (n)! := by
  rw [poissonMeasure, measureReal_def, Measure.sum_smul_dirac_singleton,
    ENNReal.toReal_ofReal (by positivity)]

lemma poissonMeasure_real_singleton_pos {r : ℝ≥0} (n : ℕ) (hr : 0 < r) :
    0 < (poissonMeasure r).real {n} := by
  rw [poissonMeasure_real_singleton]
  positivity

lemma hasSum_one_poissonMeasure (r : ℝ≥0) : HasSum (fun n ↦ exp (-r) * r ^ n / (n)!) 1 := by
  let r := r.toReal
  apply (hasSum_mul_left_iff (exp_ne_zero r)).mp
  simp only [mul_one]
  have : (fun i ↦ rexp r * (rexp (-r) * r ^ i / i.factorial)) =
      fun i ↦ r ^ i / i.factorial := by
    ext n
    rw [mul_div_assoc, exp_neg, ← mul_assoc, ← div_eq_mul_inv, div_self (exp_ne_zero r), one_mul]
  rw [this, exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp r

instance isProbabilityMeasure_poissonMeasure (r : ℝ≥0) :
    IsProbabilityMeasure (poissonMeasure r) where
  measure_univ := by
    simp only [poissonMeasure, MeasurableSpace.measurableSet_top, Measure.sum_apply,
      Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg ?_ (hasSum_one_poissonMeasure r).summable,
      (hasSum_one_poissonMeasure r).tsum_eq, ENNReal.ofReal_one]
    exact fun _ ↦ by positivity

section Integral

variable {E : Type*} [NormedAddCommGroup E]

lemma integrable_poissonMeasure_iff {r : ℝ≥0} {f : ℕ → E} :
    Integrable f (poissonMeasure r) ↔ Summable (fun n ↦ exp (-r) * r ^ n / (n)! * ‖f n‖) := by
  rw [poissonMeasure, integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n ↦ ?_ * _)
  rw [ENNReal.toReal_ofReal (by positivity)]

variable [NormedSpace ℝ E]

lemma hasSum_integral_poissonMeasure [CompleteSpace E] {r : ℝ≥0} {f : ℕ → E}
    (hf : Integrable f (poissonMeasure r)) :
    HasSum (fun n ↦ (exp (-r) * r ^ n / (n)!) • f n) (∫ n, f n ∂poissonMeasure r) := by
  have : (fun n ↦ (exp (-r) * r ^ n / (n)!) • f n) =
      fun n ↦ (ENNReal.ofReal (exp (-r) * r ^ n / (n)!)).toReal • f n := by
    ext; rw [ENNReal.toReal_ofReal (by positivity)]
  rw [this]
  apply hasSum_integral_sum_dirac (by simp)
  convert integrable_poissonMeasure_iff.1 hf
  rw [ENNReal.toReal_ofReal (by positivity)]

lemma integral_poissonMeasure' [CompleteSpace E] {r : ℝ≥0} {f : ℕ → E}
    (hf : Integrable f (poissonMeasure r)) :
    ∫ n, f n ∂poissonMeasure r = ∑' n,( exp (-r) * r ^ n / (n)!) • f n :=
  (hasSum_integral_poissonMeasure hf).tsum_eq.symm

lemma integral_poissonMeasure [FiniteDimensional ℝ E] (r : ℝ≥0) (f : ℕ → E) :
    ∫ n, f n ∂poissonMeasure r = ∑' n,( exp (-r) * r ^ n / (n)!) • f n := by
  rw [poissonMeasure, integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (by positivity)]

end Integral

section PoissonPMF

@[deprecated poissonMeasure (since := "2026-03-08")]
noncomputable
def poissonPMFReal (r : ℝ≥0) (n : ℕ) : ℝ := exp (-r) * r ^ n / (n)!

set_option linter.deprecated false in
@[deprecated hasSum_one_poissonMeasure (since := "2026-03-08")]
lemma poissonPMFRealSum (r : ℝ≥0) : HasSum (fun n ↦ poissonPMFReal r n) 1 := by
  let r := r.toReal
  unfold poissonPMFReal
  apply (hasSum_mul_left_iff (exp_ne_zero r)).mp
  simp only [mul_one]
  have : (fun i ↦ rexp r * (rexp (-r) * r ^ i / i.factorial)) =
      fun i ↦ r ^ i / i.factorial := by
    ext n
    rw [mul_div_assoc, exp_neg, ← mul_assoc, ← div_eq_mul_inv, div_self (exp_ne_zero r), one_mul]
  rw [this, exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp r

set_option linter.deprecated false in
@[deprecated poissonMeasure_real_singleton_pos (since := "2026-03-08")]
lemma poissonPMFReal_pos {r : ℝ≥0} {n : ℕ} (hr : 0 < r) : 0 < poissonPMFReal r n := by
  rw [poissonPMFReal]
  positivity

set_option linter.deprecated false in
@[deprecated measureReal_nonneg (since := "2026-03-08")]
lemma poissonPMFReal_nonneg {r : ℝ≥0} {n : ℕ} : 0 ≤ poissonPMFReal r n := by
  unfold poissonPMFReal
  positivity

set_option linter.deprecated false in
@[deprecated poissonMeasure (since := "2026-03-08")]
noncomputable
def poissonPMF (r : ℝ≥0) : PMF ℕ := by
  refine ⟨fun n ↦ ENNReal.ofReal (poissonPMFReal r n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← toNNReal_one]
  exact (poissonPMFRealSum r).toNNReal (fun n ↦ poissonPMFReal_nonneg)

set_option linter.deprecated false in
@[deprecated poissonMeasure (since := "2026-03-08")]
lemma poissonPMFReal_ofReal_eq_poissonPMF (r : ℝ≥0) (n : ℕ) :
    ENNReal.ofReal (poissonPMFReal r n) = poissonPMF r n := by
  simpa only [poissonPMF] using by rfl

set_option linter.deprecated false in
@[deprecated Measurable.of_discrete (since := "2026-03-08")]
lemma measurable_poissonPMFReal (r : ℝ≥0) : Measurable (poissonPMFReal r) := by fun_prop

set_option linter.deprecated false in
@[deprecated StronglyMeasurable.of_discrete (since := "2026-03-08")]
lemma stronglyMeasurable_poissonPMFReal (r : ℝ≥0) : StronglyMeasurable (poissonPMFReal r) :=
  stronglyMeasurable_iff_measurable.mpr (measurable_poissonPMFReal r)

end PoissonPMF

end ProbabilityTheory
