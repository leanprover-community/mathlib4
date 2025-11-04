/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-! # Poisson distributions over ℕ

Define the Poisson measure over the natural numbers

## Main definitions
* `poissonPMFReal`: the function `fun n ↦ exp (- λ) * λ ^ n / n!`
  for `n ∈ ℕ`, which is the probability density function of a Poisson distribution with
  rate `λ > 0`.
* `poissonPMF`: `ℝ≥0∞`-valued pdf,
  `poissonPMF λ = ENNReal.ofReal (poissonPMFReal λ)`.
* `poissonMeasure`: a Poisson measure on `ℕ`, parametrized by its rate `λ`.
-/

open scoped ENNReal NNReal Nat

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section PoissonPMF

/-- The pmf of the Poisson distribution depending on its rate, as a function to ℝ -/
noncomputable
def poissonPMFReal (r : ℝ≥0) (n : ℕ) : ℝ := exp (-r) * r ^ n / n !

lemma poissonPMFRealSum (r : ℝ≥0) : HasSum (fun n ↦ poissonPMFReal r n) 1 := by
  let r := r.toReal
  unfold poissonPMFReal
  apply (hasSum_mul_left_iff (exp_ne_zero r)).mp
  simp only [mul_one]
  have : (fun i ↦ rexp r * (rexp (-r) * r ^ i / ↑(Nat.factorial i))) =
      fun i ↦ r ^ i / ↑(Nat.factorial i) := by
    ext n
    rw [mul_div_assoc, exp_neg, ← mul_assoc, ← div_eq_mul_inv, div_self (exp_ne_zero r), one_mul]
  rw [this, exp_eq_exp_ℝ]
  exact NormedSpace.expSeries_div_hasSum_exp ℝ r

/-- The Poisson pmf is positive for all natural numbers -/
lemma poissonPMFReal_pos {r : ℝ≥0} {n : ℕ} (hr : 0 < r) : 0 < poissonPMFReal r n := by
  rw [poissonPMFReal]
  positivity

lemma poissonPMFReal_nonneg {r : ℝ≥0} {n : ℕ} : 0 ≤ poissonPMFReal r n := by
  unfold poissonPMFReal
  positivity

/-- The pmf of the Poisson distribution depending on its rate, as a PMF. -/
noncomputable
def poissonPMF (r : ℝ≥0) : PMF ℕ := by
  refine ⟨fun n ↦ ENNReal.ofReal (poissonPMFReal r n), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← toNNReal_one]
  exact (poissonPMFRealSum r).toNNReal (fun n ↦ poissonPMFReal_nonneg)

/-- The Poisson pmf is measurable. -/
@[fun_prop, measurability]
lemma measurable_poissonPMFReal (r : ℝ≥0) : Measurable (poissonPMFReal r) := by fun_prop

@[fun_prop, measurability]
lemma stronglyMeasurable_poissonPMFReal (r : ℝ≥0) : StronglyMeasurable (poissonPMFReal r) :=
  stronglyMeasurable_iff_measurable.mpr (measurable_poissonPMFReal r)

end PoissonPMF

/-- Measure defined by the Poisson distribution -/
noncomputable
def poissonMeasure (r : ℝ≥0) : Measure ℕ := (poissonPMF r).toMeasure

instance isProbabilityMeasurePoisson (r : ℝ≥0) :
    IsProbabilityMeasure (poissonMeasure r) := PMF.toMeasure.isProbabilityMeasure (poissonPMF r)

end ProbabilityTheory
