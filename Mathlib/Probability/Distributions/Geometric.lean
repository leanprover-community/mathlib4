/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/

import Mathlib.Probability.Notation

/-! # Geometric distributions over ℕ

Define the geometric measure over the natural numbers

## Main definitions
* `geometricPmfReal`: the function `p x ↦ (1-p) ^ x * p`
  for `x ∈ ℕ`, which is the probability density function of a geometric distribution with
  success probability `p ∈ (0,1]`.
* `geometricPmf`: `ℝ≥0∞`-valued pdf,
  `geometricPmf p = ENNReal.ofReal (geometricPmfReal p)`.
* `geometricMeasure`: a geometric measure on `ℕ`, parametrized by its success probability `p`.
-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section PoissonPmf

/-- The pmf of the geometric distribution depending on its success probability. -/
noncomputable
def geometricPmfReal (p : Ioc 0 1) (x : ℕ) : ℝ := (1-p) ^ x * p

lemma geometricPmfRealSum (p : Ioc 0 1) : HasSum (fun x ↦ geometricPmfReal p x) 1 := by
  unfold geometricPmfReal
  sorry

/-- The Poisson pmf is positive for all natural numbers -/
lemma poissonPmfReal_pos {r : ℝ≥0} {x : ℕ} (hr : 0 < r) : 0 < poissonPmfReal r x := by
  rw [poissonPmfReal]
  positivity

lemma poissonPmfReal_nonneg {r : ℝ≥0} {x : ℕ} : 0 ≤ poissonPmfReal r x := by
  unfold poissonPmfReal
  positivity

/-- Geometric distribution with success probability `p`. -/
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
