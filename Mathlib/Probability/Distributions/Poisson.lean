/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/

import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Basic

/-! # Poisson distributions over ℕ

Define the Poisson measure over the natural numbers

## Main definitions
* `poissonPmfReal`: the function `λ n ↦ exp (- λ) * λ ^ n / n!`
  for `n ∈ ℕ`, which is the probability density function of a Poisson distribution with
  rate `λ > 0`.
* `poissonPmf`: `ℝ≥0∞`-valued pdf,
  `poissonPmf λ = ENNReal.ofReal (poissonPmfReal λ)`.
* `poissonMeasure`: a Poisson measure on `ℕ`, parametrized by its rate `λ`.
-/

open scoped ENNReal NNReal Nat

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section PoissonPmf

/-- The pmf of the Poisson distribution depending on its rate, as a function to ℝ -/
noncomputable
def poissonPmfReal (r : ℝ≥0) (n : ℕ) : ℝ := (exp (- r) * r ^ n / n !)

lemma poissonPmfRealSum (r : ℝ≥0) : HasSum (fun n ↦ poissonPmfReal r n) 1 := by
  let r := r.toReal
  unfold poissonPmfReal
  apply (hasSum_mul_left_iff (exp_ne_zero r)).mp
  simp only [mul_one]
  have : (fun i ↦ rexp r * (rexp (-r) * r ^ i / ↑(Nat.factorial i))) =
      fun i ↦ r ^ i / ↑(Nat.factorial i) := by
    ext n
    rw [mul_div_assoc, exp_neg, ← mul_assoc, ← div_eq_mul_inv, div_self (exp_ne_zero r), one_mul]
  rw [this, exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp ℝ r

/-- The Poisson pmf is positive for all natural numbers -/
lemma poissonPmfReal_pos {r : ℝ≥0} {n : ℕ} (hr : 0 < r) : 0 < poissonPmfReal r n := by
  rw [poissonPmfReal]
  positivity

lemma poissonPmfReal_nonneg {r : ℝ≥0} {n : ℕ} : 0 ≤ poissonPmfReal r n := by
  unfold poissonPmfReal
  positivity

/-- The pmf of the Poisson distribution depending on its rate, as a PMF. -/
noncomputable
def poissonPmf (r : ℝ≥0) : PMF ℕ := by
  refine ⟨fun n ↦ ENNReal.ofReal (poissonPmfReal r n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← toNNReal_one]
  exact (poissonPmfRealSum r).toNNReal (fun n ↦ poissonPmfReal_nonneg)

/-- The Poisson pmf is measurable. -/
@[measurability]
lemma measurable_poissonPmfReal (r : ℝ≥0) : Measurable (poissonPmfReal r) := by measurability

@[measurability]
lemma stronglyMeasurable_poissonPmfReal (r : ℝ≥0) : StronglyMeasurable (poissonPmfReal r) :=
  stronglyMeasurable_iff_measurable.mpr (measurable_poissonPmfReal r)

end PoissonPmf

/-- Measure defined by the Poisson distribution -/
noncomputable
def poissonMeasure (r : ℝ≥0) : Measure ℕ := (poissonPmf r).toMeasure

instance isProbabilityMeasurePoisson (r : ℝ≥0) :
    IsProbabilityMeasure (poissonMeasure r) := PMF.toMeasure.isProbabilityMeasure (poissonPmf r)

end ProbabilityTheory
