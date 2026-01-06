/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

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

@[expose] public section

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
  exact NormedSpace.expSeries_div_hasSum_exp r

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

theorem poissonPMF_apply {r : ℝ≥0} {n : ℕ} :
  poissonPMF r n = ENNReal.ofReal (poissonPMFReal r n) := rfl

/-- The Poisson pmf is measurable. -/
@[fun_prop]
lemma measurable_poissonPMFReal (r : ℝ≥0) : Measurable (poissonPMFReal r) := by fun_prop

@[fun_prop]
lemma stronglyMeasurable_poissonPMFReal (r : ℝ≥0) : StronglyMeasurable (poissonPMFReal r) :=
  stronglyMeasurable_iff_measurable.mpr (measurable_poissonPMFReal r)

lemma poissonPMFReal_mul_eq_succ_mul (r : ℝ≥0) (n : ℕ) :
    poissonPMFReal r n * r = poissonPMFReal r (n + 1) * ↑(n + 1) := by
  simp [poissonPMFReal, Nat.factorial_succ, pow_succ]
  field_simp

theorem poissonPMFReal_hasSum_nmul (r : ℝ≥0) : HasSum (fun n ↦ poissonPMFReal r n * n) r := by
  suffices HasSum _ (poissonPMFReal r 0 * (0 : ℕ) + 1 * r) by simpa using this
  apply HasSum.zero_add
  simpa only [← poissonPMFReal_mul_eq_succ_mul] using (poissonPMFRealSum r).mul_right r.toReal

theorem poissonPMF_tsum_nmul (r : ℝ≥0) : ∑' n, poissonPMF r n * n = r := by
  simp_rw [poissonPMF_apply, ENNReal.ofReal_eq_coe_nnreal poissonPMFReal_nonneg]
  exact ENNReal.tsum_coe_eq <| NNReal.hasSum_coe.mp <| poissonPMFReal_hasSum_nmul r

theorem poissonPMF_coe_tsum_nmul (r : ℝ≥0) : ∑' n, (poissonPMF r n).toReal * n = r := by
  simp_rw [poissonPMF_apply, ENNReal.ofReal_eq_coe_nnreal poissonPMFReal_nonneg]
  exact (poissonPMFReal_hasSum_nmul r).tsum_eq

end PoissonPMF

/-- Measure defined by the Poisson distribution -/
noncomputable
def poissonMeasure (r : ℝ≥0) : Measure ℕ := (poissonPMF r).toMeasure

instance isProbabilityMeasurePoisson (r : ℝ≥0) :
    IsProbabilityMeasure (poissonMeasure r) := PMF.toMeasure.isProbabilityMeasure (poissonPMF r)

end ProbabilityTheory
