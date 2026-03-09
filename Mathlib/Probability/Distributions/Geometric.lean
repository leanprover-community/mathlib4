/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Basic

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Geometric distributions over ℕ

Define the geometric measure over the natural numbers. For `0 < p ≤ 1`, `geometricMeasure p` is the
measure which to `{n}` associates `(1 - p) ^ n * n`.

## Main definition

* `geometricMeasure p`: a geometric measure on `ℕ`, parametrized by its success probability `p`.

## Implementation note

In order to automatically infer `IsProbabilityMeasure (geometricMeasure p)`, we define
`geometricMeasure p` for a general `p : ℝ` and set it to `Measure.dirac 0` if `p ≤ 0` or `1 < p`.
Use `geometricMeasure_eq` to rewrite the measure as a sum of Dirac masses.
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

variable {p : ℝ}

/-- The geometric measure with success probability `p` as a measure over `ℕ`. -/
noncomputable def geometricMeasure (p : ℝ) : Measure ℕ := if 0 < p ∧ p ≤ 1
  then
    Measure.sum (fun n ↦ ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n)
  else
    .dirac 0

lemma geometricMeasure_eq (h1 : 0 < p) (h2 : p ≤ 1) :
    geometricMeasure p = Measure.sum (fun n ↦ ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n) :=
  if_pos ⟨h1, h2⟩

/-- The `positivty` tactic does not work for this goal. Use this lemma to rewrite
`(ENNReal.ofReal ((1 - p) ^ n * p)).toReal = (1 - p) ^ n * p)`. -/
lemma geometricMeasure_nonneg (h1 : 0 < p) (h2 : p ≤ 1) (n : ℕ) :
    0 ≤ (1 - p) ^ n * p := by positivity [pow_nonneg (a := 1 - p) (by linarith) n]

lemma geometricMeasure_pos (h1 : 0 < p) (h2 : p < 1) (n : ℕ) :
    0 < (1 - p) ^ n * p := by positivity [pow_pos (a := 1 - p) (by linarith) n]

lemma geometricMeasure_real_singleton (h1 : 0 < p) (h2 : p ≤ 1) (n : ℕ) :
    (geometricMeasure p).real {n} = (1 - p) ^ n * p := by
  rw [geometricMeasure, if_pos ⟨h1, h2⟩, measureReal_def, Measure.sum_smul_dirac_singleton,
    ENNReal.toReal_ofReal (geometricMeasure_nonneg h1 h2 n)]

lemma geometricMeasure_real_singleton_pos (n : ℕ) (h1 : 0 < p) (h2 : p < 1) :
    0 < (geometricMeasure p).real {n} := by
  rw [geometricMeasure_real_singleton h1 h2.le]
  exact geometricMeasure_pos h1 h2 n

lemma hasSum_one_geometricMeasure (h1 : 0 < p) (h2 : p ≤ 1) :
    HasSum (fun n ↦ (1 - p) ^ n * p) 1 := by
  convert (hasSum_geometric_of_lt_one (r := 1 - p) (by linarith) (by linarith)).mul_right p
  simp [field]

instance isProbabilityMeasure_geometricMeasure :
    IsProbabilityMeasure (geometricMeasure p) := by
  rw [geometricMeasure]
  split_ifs with h
  · exact (hasSum_one_geometricMeasure h.1 h.2).isProbabilityMeasure_sum_dirac
      (geometricMeasure_nonneg h.1 h.2)
  · infer_instance

section Integral

variable {E : Type*} [NormedAddCommGroup E]

lemma integrable_geometricMeasure_iff (h1 : 0 < p) (h2 : p ≤ 1) {f : ℕ → E} :
    Integrable f (geometricMeasure p) ↔ Summable (fun n ↦ (1 - p) ^ n * p * ‖f n‖) := by
  rw [geometricMeasure_eq h1 h2, integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n ↦ ?_ * _)
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg h1 h2 n)]

variable [NormedSpace ℝ E]

lemma hasSum_integral_geometricMeasure [CompleteSpace E] {f : ℕ → E}
    (h1 : 0 < p) (h2 : p ≤ 1) (hf : Integrable f (geometricMeasure p)) :
    HasSum (fun n ↦ ((1 - p) ^ n * p) • f n) (∫ n, f n ∂geometricMeasure p) := by
  have : (fun n ↦ ((1 - p) ^ n * p) • f n) =
      fun n ↦ (ENNReal.ofReal ((1 - p) ^ n * p)).toReal • f n := by
    ext n; rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg h1 h2 n)]
  rw [this, geometricMeasure_eq h1 h2]
  apply hasSum_integral_sum_dirac (by simp)
  convert (integrable_geometricMeasure_iff h1 h2).1 hf with n
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg h1 h2 n)]

lemma integral_geometricMeasure' [CompleteSpace E] {f : ℕ → E} (h1 : 0 < p) (h2 : p ≤ 1)
    (hf : Integrable f (geometricMeasure p)) :
    ∫ n, f n ∂geometricMeasure p = ∑' n, ((1 - p) ^ n * p) • f n :=
  (hasSum_integral_geometricMeasure h1 h2 hf).tsum_eq.symm

lemma integral_geometricMeasure [FiniteDimensional ℝ E] (h1 : 0 < p) (h2 : p ≤ 1) (f : ℕ → E) :
    ∫ n, f n ∂geometricMeasure p = ∑' n, ((1 - p) ^ n * p) • f n := by
  rw [geometricMeasure_eq h1 h2, integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg h1 h2 n)]

end Integral

section GeometricPMF

/-- The pmf of the geometric distribution depending on its success probability. -/
@[deprecated geometricMeasure (since := "2026-03-08")]
noncomputable
def geometricPMFReal (p : ℝ) (n : ℕ) : ℝ := (1 - p) ^ n * p

set_option linter.deprecated false in
@[deprecated hasSum_one_geometricMeasure (since := "2026-03-08")]
lemma geometricPMFRealSum (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    HasSum (fun n ↦ geometricPMFReal p n) 1 := by
  unfold geometricPMFReal
  have := hasSum_geometric_of_lt_one (sub_nonneg.mpr hp_le_one) (sub_lt_self 1 hp_pos)
  apply (hasSum_mul_right_iff (hp_pos.ne')).mpr at this
  simp only [sub_sub_cancel] at this
  rw [inv_mul_eq_div, div_self hp_pos.ne'] at this
  exact this

set_option linter.deprecated false in
@[deprecated geometricMeasure_real_singleton_pos (since := "2026-03-08")]
lemma geometricPMFReal_pos {n : ℕ} (hp_pos : 0 < p) (hp_lt_one : p < 1) :
    0 < geometricPMFReal p n := by
  rw [geometricPMFReal]
  positivity [sub_pos.mpr hp_lt_one]

set_option linter.deprecated false in
@[deprecated measureReal_nonneg (since := "2026-03-08")]
lemma geometricPMFReal_nonneg {n : ℕ} (hp_pos : 0 < p) (hp_le_one : p ≤ 1) :
    0 ≤ geometricPMFReal p n := by
  rw [geometricPMFReal]
  positivity [sub_nonneg.mpr hp_le_one]

set_option linter.deprecated false in
/-- Geometric distribution with success probability `p`. -/
@[deprecated geometricMeasure (since := "2026-03-08")]
noncomputable
def geometricPMF (hp_pos : 0 < p) (hp_le_one : p ≤ 1) : PMF ℕ :=
  ⟨fun n ↦ ENNReal.ofReal (geometricPMFReal p n), by
    apply ENNReal.hasSum_coe.mpr
    rw [← toNNReal_one]
    exact (geometricPMFRealSum hp_pos hp_le_one).toNNReal
      (fun n ↦ geometricPMFReal_nonneg hp_pos hp_le_one)⟩

set_option linter.deprecated false in
@[deprecated Measurable.of_discrete (since := "2026-03-08")]
lemma measurable_geometricPMFReal : Measurable (geometricPMFReal p) := by
  fun_prop

set_option linter.deprecated false in
@[deprecated StronglyMeasurable.of_discrete (since := "2026-03-08")]
lemma stronglyMeasurable_geometricPMFReal : StronglyMeasurable (geometricPMFReal p) :=
  stronglyMeasurable_iff_measurable.mpr measurable_geometricPMFReal

end GeometricPMF

@[deprecated (since := "2025-08-28")] alias isProbabilityMeasureGeometric :=
  isProbabilityMeasure_geometricMeasure

end ProbabilityTheory
