/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Probability.Distributions.Geometric
public import Mathlib.Probability.Moments.Variance

import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Moments of the geometric distribution

We compute the mean and the variance of `geometricMeasure p`, the law of the number of failures
before the first success in independent trials with success probability `p`.

## Main statements

* `integral_id_geometricMeasure`: the mean of `geometricMeasure p` is `(1 - p) / p`.
* `variance_id_geometricMeasure`: the variance of `geometricMeasure p` is `(1 - p) / p ^ 2`.

Both hold for every `p : unitInterval`: for `p = 0`, `geometricMeasure 0 = dirac 0` and both
sides vanish.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {p : unitInterval}

private lemma norm_one_sub_lt_one (hp : p ≠ 0) : ‖(1 - p : ℝ)‖ < 1 := by
  have : (0 : ℝ) < p := lt_of_le_of_ne p.2.1 fun h ↦ hp (Subtype.ext h.symm)
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [p.2.2]

lemma hasSum_coe_mul_geometricMeasure (hp : p ≠ 0) :
    HasSum (fun n : ℕ ↦ ((1 - p : ℝ) ^ n * p) * n) ((1 - p) / p) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (norm_one_sub_lt_one hp)).mul_left (p : ℝ)
  rw [sub_sub_cancel] at h
  have hp' : (p : ℝ) ≠ 0 := fun h ↦ hp (Subtype.ext h)
  rw [show (1 - p : ℝ) / p = p * ((1 - p) / p ^ 2) by field_simp]
  exact h.congr_fun fun n ↦ by ring

lemma hasSum_sq_mul_geometricMeasure (hp : p ≠ 0) :
    HasSum (fun n : ℕ ↦ ((1 - p : ℝ) ^ n * p) * (n : ℝ) ^ 2) ((1 - p) * (2 - p) / p ^ 2) := by
  have h := (hasSum_sq_mul_geometric_of_norm_lt_one (norm_one_sub_lt_one hp)).mul_left (p : ℝ)
  rw [sub_sub_cancel] at h
  have hp' : (p : ℝ) ≠ 0 := fun h ↦ hp (Subtype.ext h)
  rw [show (1 - p : ℝ) * (2 - p) / p ^ 2 = p * ((1 - p) * (1 + (1 - p)) / p ^ 3) by
    field_simp; ring]
  exact h.congr_fun fun n ↦ by ring

/-- The mean of the geometric distribution with success probability `p` is `(1 - p) / p`. -/
lemma integral_id_geometricMeasure : ∫ n, (n : ℝ) ∂geometricMeasure p = (1 - p) / p := by
  by_cases hp : p = 0
  · simp [geometricMeasure, hp]
  rw [integral_geometricMeasure hp]
  simpa using (hasSum_coe_mul_geometricMeasure hp).tsum_eq

lemma integral_sq_geometricMeasure :
    ∫ n, (n : ℝ) ^ 2 ∂geometricMeasure p = (1 - p) * (2 - p) / p ^ 2 := by
  by_cases hp : p = 0
  · simp [geometricMeasure, hp]
  rw [integral_geometricMeasure hp]
  simpa using (hasSum_sq_mul_geometricMeasure hp).tsum_eq

lemma memLp_two_id_geometricMeasure : MemLp (fun n : ℕ ↦ (n : ℝ)) 2 (geometricMeasure p) := by
  by_cases hp : p = 0
  · simp only [geometricMeasure, hp, ne_eq, not_true_eq_false, ↓reduceIte]
    exact .of_bound (by fun_prop) 0 ((ae_dirac_iff .of_discrete).2 (by simp))
  refine (memLp_two_iff_integrable_sq (by fun_prop)).2 ?_
  rw [integrable_geometricMeasure_iff hp]
  simpa using (hasSum_sq_mul_geometricMeasure hp).summable

/-- The variance of the geometric distribution with success probability `p`
is `(1 - p) / p ^ 2`. -/
lemma variance_id_geometricMeasure :
    Var[fun n : ℕ ↦ (n : ℝ); geometricMeasure p] = (1 - p) / p ^ 2 := by
  rw [variance_eq_sub memLp_two_id_geometricMeasure]
  simp only [Pi.pow_apply, integral_sq_geometricMeasure, integral_id_geometricMeasure]
  by_cases hp : (p : ℝ) = 0
  · simp [hp]
  field_simp
  ring

end ProbabilityTheory
