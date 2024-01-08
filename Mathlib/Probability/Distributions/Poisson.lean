/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/

import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.Notation

/-! # Poisson distributions over ℝ

Define the Poisson measure over the reals

## Main definitions
* `poissonPmfReal`: the function `λ x ↦ exp (- λ) * λ ^ x / x!`
  for `x ∈ ℕ`, which is the probability density function of a Poisson distribution with
  rate `λ > 0`.
* `poissonPmf`: `ℝ≥0∞`-valued pdf,
  `poissonPmf λ = ENNReal.ofReal (poissonPmfReal λ)`.
* `poissonMeasure`: a Poisson measure on `ℝ`, parametrized by its rate `λ`.
-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section PoissonPmf

/-- The pmf of the Poisson distribution depending on its rate-/
noncomputable
def poissonPmfReal (r : ℝ≥0) (x : ℕ) : ℝ := (exp (- r) * r ^ x / (Nat.factorial x))

lemma poissonPmfRealSum (r : ℝ≥0) : HasSum (fun x ↦ poissonPmfReal r x) 1 := by
  let r := r.toReal
  unfold poissonPmfReal
  apply (hasSum_mul_left_iff (exp_ne_zero (r))).mp
  simp only [mul_one]
  have : (fun i ↦ rexp r * (rexp (-r) * r ^ i / ↑(Nat.factorial i))) =
      fun i ↦ r ^ i / ↑(Nat.factorial i) := by
    ext x
    rw [mul_div_assoc, exp_neg, ← mul_assoc, ← div_eq_mul_inv, div_self (exp_ne_zero r), one_mul]
  rw [this, exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp ℝ r

/-- The Poisson pmf is positive for all natural numbers -/
lemma poissonPmfReal_pos {r : ℝ≥0} {x : ℕ} (hr : 0 < r) : 0 < poissonPmfReal r x := by
  rw [poissonPmfReal]
  positivity

lemma poissonPmfReal_nonneg {r : ℝ≥0} {x : ℕ} : 0 ≤ poissonPmfReal r x := by
  unfold poissonPmfReal
  positivity

noncomputable
def poissonPmf (r : ℝ≥0) : PMF ℕ := by
  refine ⟨fun x ↦ ENNReal.ofReal (poissonPmfReal r x), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← toNNReal_one]
  exact (poissonPmfRealSum r).toNNReal (fun n ↦ poissonPmfReal_nonneg)

/-- The Poisson pmf is measurable. -/
lemma measurable_poissonPmfReal (r : ℝ≥0) : Measurable (poissonPmfReal r) := by measurability

lemma stronglyMeasurable_poissonPmfReal (r : ℝ≥0) : StronglyMeasurable (poissonPmfReal r) :=
  stronglyMeasurable_iff_measurable.mpr (measurable_poissonPmfReal r)

/-- Measure defined by the Poisson distribution -/
noncomputable
def poissonMeasure (r : ℝ≥0) : Measure ℕ :=
  if r > 0 then (poissonPmf r).toMeasure else Measure.dirac 0

lemma poissonMeasure_of_rate_ne_zero {r : ℝ≥0} (hr : r > 0) :
    poissonMeasure r = (poissonPmf r).toMeasure := if_pos hr

lemma poissonMeasure_of_rate_zero :
    poissonMeasure 0 = Measure.dirac 0 := if_neg not_lt_zero'

lemma isProbabilityMeasurePoisson (r : ℝ≥0) :
    IsProbabilityMeasure (poissonMeasure r) := by
  by_cases h : r > 0
  · rw [poissonMeasure_of_rate_ne_zero h]
    exact PMF.toMeasure.isProbabilityMeasure (poissonPmf r)
  · rw [le_zero_iff.mp (not_lt.mp h), poissonMeasure_of_rate_zero]
    exact Measure.dirac.isProbabilityMeasure
