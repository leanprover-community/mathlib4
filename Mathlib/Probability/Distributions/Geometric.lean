/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.ProbabilityMassFunction.Basic

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Geometric distributions

We define the geometric distributions over natural numbers. For `0 < p ≤ 1`, `geometricMeasure p`
is the measure which to `{n}` associates `(1 - p) ^ n * p`.

As the parameter `p` needs to lie between `0` and `1`, we define `geometricMeasure p` with
`p : unitInterval`.

Imagine a certain experiment which has success probability `p`. If you repeat this experiment
infinitely many times and independently, the number of failures before the first success
follows a geometric distribution with parameter `p`.

## Main definition

* `geometricMeasure p`: a geometric measure on `ℕ`,
  parametrized by its success probability `p`.

## Main statements

* `integral_id_geometricMeasure`: the mean of `geometricMeasure p` is `(1 - p) / p`.
* `variance_id_geometricMeasure`: the variance of `geometricMeasure p` is `(1 - p) / p ^ 2`.

## Implementation note

To avoid having to carry around a hypothesis `p ≠ 0`, we define
`geometricMeasure 0 := Measure.dirac 0`. That way `IsProbabilityMeasure (geometricMeasure p)`
can be automatically inferred.

## Tags

geometric distribution
-/

@[expose] public section

open scoped ENNReal NNReal

open MeasureTheory Real Set

namespace ProbabilityTheory

variable {p : unitInterval}

/-- The geometric measure with success probability `p` as a measure over `ℕ`. -/
noncomputable def geometricMeasure (p : unitInterval) : Measure ℕ := if p ≠ 0
  then
    Measure.sum (fun n ↦ ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n)
  else
    .dirac 0

lemma geometricMeasure_eq (hp : p ≠ 0) :
    geometricMeasure p =
      Measure.sum (fun n ↦ ENNReal.ofReal ((1 - p) ^ n * p) • .dirac n) :=
  ite_eq_left hp

/-- The `positivity` tactic does not work for this goal. Use this lemma to rewrite
`(ENNReal.ofReal ((1 - p) ^ n * p)).toReal = (1 - p) ^ n * p`. -/
lemma geometricMeasure_nonneg (p : unitInterval) n :
    0 ≤ (1 - p : ℝ) ^ n * p := mul_nonneg (pow_nonneg (by grind) n) p.2.1

lemma geometricMeasure_pos (h1 : p ≠ 0) (h2 : p ≠ 1) n :
    0 < (1 - p : ℝ) ^ n * p := mul_pos (pow_pos (by grind) n) (by grind)

lemma geometricMeasure_singleton (hp : p ≠ 0) n :
    geometricMeasure p {n} = ENNReal.ofReal ((1 - p) ^ n * p) := by
  rw [geometricMeasure_eq hp, Measure.sum_smul_dirac_singleton]

lemma geometricMeasure_real_singleton (hp : p ≠ 0) n :
    (geometricMeasure p).real {n} = (1 - p) ^ n * p := by
  rw [measureReal_def, geometricMeasure_singleton hp,
    ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

lemma geometricMeasure_real_singleton_pos (h1 : p ≠ 0) (h2 : p ≠ 1) n :
    0 < (geometricMeasure p).real {n} := by
  rw [geometricMeasure_real_singleton h1]
  exact geometricMeasure_pos h1 h2 n

lemma hasSum_one_geometricMeasure (hp : p ≠ 0) :
    HasSum (fun n ↦ (1 - p : ℝ) ^ n * p) 1 := by
  convert (hasSum_geometric_of_lt_one (r := 1 - p) (by grind) (by grind)).mul_right (p : ℝ)
  grind

instance isProbabilityMeasure_geometricMeasure :
    IsProbabilityMeasure (geometricMeasure p) := by
  rw [geometricMeasure]
  split_ifs with h
  · exact (hasSum_one_geometricMeasure h).isProbabilityMeasure_sum_dirac
      (geometricMeasure_nonneg p)
  · infer_instance

section Integral

variable {E : Type*} [NormedAddCommGroup E] {f : ℕ → E}

lemma integrable_geometricMeasure_iff (hp : p ≠ 0) :
    Integrable f (geometricMeasure p) ↔ Summable (fun n ↦ (1 - p : ℝ) ^ n * p * ‖f n‖) := by
  rw [geometricMeasure_eq hp, integrable_sum_dirac_iff (by simp)]
  congrm Summable (fun n ↦ ?_ * _)
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

variable [NormedSpace ℝ E]

lemma hasSum_integral_geometricMeasure [CompleteSpace E]
    (hp : p ≠ 0) (hf : Integrable f (geometricMeasure p)) :
    HasSum (fun n ↦ ((1 - p : ℝ) ^ n * p) • f n) (∫ n, f n ∂geometricMeasure p) := by
  have : (fun n ↦ ((1 - p : ℝ) ^ n * p) • f n) =
      fun n ↦ (ENNReal.ofReal ((1 - p) ^ n * p)).toReal • f n := by
    ext n; rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]
  rw [this, geometricMeasure_eq hp]
  apply hasSum_integral_sum_dirac (by simp)
  convert! (integrable_geometricMeasure_iff hp).1 hf with n
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

/-- If a function is integrable with respect to `geometricMeasure p`, then its integral
against this measure is given by its sum weighted by `(1 - p) ^ n * p`.

See `integral_geometricMeasure` for a version where the codomain is finite-dimensional
and does not require the integrability hypothesis. -/
lemma integral_geometricMeasure' [CompleteSpace E] (hp : p ≠ 0)
    (hf : Integrable f (geometricMeasure p)) :
    ∫ n, f n ∂geometricMeasure p = ∑' n : ℕ, ((1 - p : ℝ) ^ n * p) • f n :=
  (hasSum_integral_geometricMeasure hp hf).tsum_eq.symm

/-- The integral of a function taking values in a finite-dimensional space
against `geometricMeasure p` is given by its sum weighted by `(1 - p) ^ n * p`. This version
does not require integrability, as the integral exists if and only if the sum exists, and otherwise
they are both defined to be zero.

See `integral_geometricMeasure'` with a general codomain which assumes integrability. -/
lemma integral_geometricMeasure [FiniteDimensional ℝ E] (hp : p ≠ 0) (f : ℕ → E) :
    ∫ n, f n ∂geometricMeasure p = ∑' n : ℕ, ((1 - p : ℝ) ^ n * p) • f n := by
  rw [geometricMeasure_eq hp, integral_sum_dirac (by simp)]
  congr with n
  rw [ENNReal.toReal_ofReal (geometricMeasure_nonneg p n)]

end Integral

section Moments

private lemma norm_one_sub_lt_one (hp : p ≠ 0) : ‖(1 - p : ℝ)‖ < 1 := by
  have : (0 : ℝ) < p := lt_of_le_of_ne p.2.1 fun h ↦ hp (Subtype.ext h.symm)
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [p.2.2]

/-- The series computing the mean of `geometricMeasure p`. -/
lemma hasSum_coe_mul_geometricMeasure (hp : p ≠ 0) :
    HasSum (fun n : ℕ ↦ ((1 - p : ℝ) ^ n * p) * n) ((1 - p) / p) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (norm_one_sub_lt_one hp)).mul_left (p : ℝ)
  rw [sub_sub_cancel] at h
  have hp' : (p : ℝ) ≠ 0 := fun h ↦ hp (Subtype.ext h)
  rw [show (1 - p : ℝ) / p = p * ((1 - p) / p ^ 2) by field_simp]
  exact h.congr_fun fun n ↦ by ring

/-- The series computing the second moment of `geometricMeasure p`. -/
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

/-- The second moment of `geometricMeasure p` is `(1 - p) * (2 - p) / p ^ 2`. -/
lemma integral_sq_geometricMeasure :
    ∫ n, (n : ℝ) ^ 2 ∂geometricMeasure p = (1 - p) * (2 - p) / p ^ 2 := by
  by_cases hp : p = 0
  · simp [geometricMeasure, hp]
  rw [integral_geometricMeasure hp]
  simpa using (hasSum_sq_mul_geometricMeasure hp).tsum_eq

/-- A geometric random variable has a finite second moment. -/
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
  simp only [Pi.pow_apply]
  rw [integral_sq_geometricMeasure, integral_id_geometricMeasure]
  by_cases hp : (p : ℝ) = 0
  · simp [hp]
  field_simp
  ring

end Moments

end ProbabilityTheory
