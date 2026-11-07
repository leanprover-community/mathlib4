/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance

/-!
# Moments of the Poisson distribution

We compute the factorial moments and the first few raw and central moments of the Poisson
distribution with rate `r : ℝ≥0`.

## Main results

* `integral_descFactorial_poissonMeasure`: the factorial moments of the Poisson distribution,
  `∫ n, n (n - 1) ⋯ (n - k + 1) ∂Po(r) = r ^ k`.
* `memLp_id_map_cast_poissonMeasure`: a Poisson random variable has moments of all orders.
* `integral_pow_map_cast_poissonMeasure`: the raw moments of the Poisson distribution are given by
  the Touchard polynomials, `∫ x, x ^ k ∂Po(ℝ, r) = ∑ j ∈ range (k + 1), S(k, j) * r ^ j`, where
  `S(k, j) = Nat.stirlingSecond k j` are the Stirling numbers of the second kind.
* `integral_id_map_cast_poissonMeasure`, `integral_pow_two_map_cast_poissonMeasure`,
  `integral_pow_three_map_cast_poissonMeasure`, `integral_pow_four_map_cast_poissonMeasure`:
  the raw moments of order `1` to `4`.
* `variance_id_map_cast_poissonMeasure`: the variance of `Po(r)` is `r`.
* `centralMoment_three_map_cast_poissonMeasure`, `centralMoment_four_map_cast_poissonMeasure`:
  the central moments of order `3` and `4` are `r` and `3 * r ^ 2 + r`.
-/

public section

open MeasureTheory Real
open scoped NNReal Nat

namespace ProbabilityTheory

/-- The factorial moments of the Poisson distribution, as a sum: the sequence
`n ↦ exp (-r) * r ^ n / n! * n (n - 1) ⋯ (n - k + 1)` has sum `r ^ k`. -/
lemma hasSum_mul_descFactorial_poissonMeasure (r : ℝ≥0) (k : ℕ) :
    HasSum (fun n ↦ exp (-r) * r ^ n / n ! * (n.descFactorial k : ℝ)) (r ^ k) := by
  rw [← hasSum_nat_add_iff' k]
  have h0 : ∑ i ∈ Finset.range k, exp (-r) * r ^ i / i ! * (i.descFactorial k : ℝ) = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by
      simp [Nat.descFactorial_eq_zero_iff_lt.2 (Finset.mem_range.1 hi)]
  rw [h0, sub_zero]
  convert (hasSum_one_poissonMeasure r).mul_left ((r : ℝ) ^ k) using 1
  · ext n
    have h := Nat.factorial_mul_descFactorial (Nat.le_add_left k n)
    rw [Nat.add_sub_cancel] at h
    rw [← h]
    push_cast
    have : ((n + k).descFactorial k : ℝ) ≠ 0 := by
      exact_mod_cast Nat.descFactorial_eq_zero_iff_lt.not.2 (by omega)
    field_simp
    ring
  · ring

/-- The factorial moments of the Poisson distribution:
`∫ n, n (n - 1) ⋯ (n - k + 1) ∂Po(r) = r ^ k`. -/
lemma integral_descFactorial_poissonMeasure (r : ℝ≥0) (k : ℕ) :
    ∫ n, (n.descFactorial k : ℝ) ∂Po(r) = r ^ k := by
  rw [integral_poissonMeasure]
  simpa using (hasSum_mul_descFactorial_poissonMeasure r k).tsum_eq

/-- The Poisson distribution has exponential moments of all orders. -/
lemma integrable_exp_mul_map_cast_poissonMeasure (r : ℝ≥0) (t : ℝ) :
    Integrable (fun x ↦ exp (t * x)) Po(ℝ, r) := by
  rw [integrable_map_measure (by fun_prop) .of_discrete, integrable_poissonMeasure_iff]
  convert (Real.summable_pow_div_factorial (r * exp t)).mul_left (exp (-r)) using 2 with n
  simp only [Function.comp_apply, norm_eq_abs, mul_comm t, exp_nat_mul, abs_pow, abs_exp, mul_pow]
  ring

/-- The moment generating function of the Poisson distribution is finite everywhere. -/
lemma integrableExpSet_id_map_cast_poissonMeasure (r : ℝ≥0) :
    integrableExpSet id Po(ℝ, r) = Set.univ :=
  Set.eq_univ_of_forall (integrable_exp_mul_map_cast_poissonMeasure r)

/-- A Poisson random variable has finite moments of all orders. -/
lemma memLp_id_map_cast_poissonMeasure (r : ℝ≥0) (p : ℝ≥0) : MemLp id p Po(ℝ, r) :=
  memLp_of_mem_interior_integrableExpSet (by simp [integrableExpSet_id_map_cast_poissonMeasure]) p

/-- All the moments of the Poisson distribution are finite. -/
lemma integrable_pow_map_cast_poissonMeasure (r : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ k) Po(ℝ, r) :=
  integrable_pow_of_mem_interior_integrableExpSet
    (X := id) (by simp [integrableExpSet_id_map_cast_poissonMeasure]) k

/-- Compute an integral against `Po(ℝ, r)` of a function whose weighted sum is known. -/
private lemma integral_map_cast_poissonMeasure_of_hasSum {r : ℝ≥0} {f : ℝ → ℝ} {a : ℝ}
    (hf : Measurable f) (h : HasSum (fun n : ℕ ↦ exp (-r) * r ^ n / n ! * f n) a) :
    ∫ x, f x ∂Po(ℝ, r) = a := by
  rw [integral_map .of_discrete hf.aestronglyMeasurable, integral_poissonMeasure]
  exact h.tsum_eq

/-- The raw moments of the Poisson distribution, as a sum: the sequence
`n ↦ exp (-r) * r ^ n / n! * n ^ k` has sum `∑ j ∈ range (k + 1), S(k, j) * r ^ j`, where
`S(k, j) = Nat.stirlingSecond k j`. -/
lemma hasSum_mul_pow_poissonMeasure (r : ℝ≥0) (k : ℕ) :
    HasSum (fun n ↦ exp (-r) * r ^ n / n ! * (n : ℝ) ^ k)
      (∑ j ∈ Finset.range (k + 1), (Nat.stirlingSecond k j : ℝ) * r ^ j) := by
  convert hasSum_sum fun j _ ↦
    (hasSum_mul_descFactorial_poissonMeasure r j).mul_left (Nat.stirlingSecond k j : ℝ) with n
  rw [← Nat.cast_pow, Nat.pow_eq_sum_stirlingSecond_mul_descFactorial, Nat.cast_sum,
    Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The raw moments of the Poisson distribution are given by the Touchard polynomials:
`∫ x, x ^ k ∂Po(ℝ, r) = ∑ j ∈ range (k + 1), S(k, j) * r ^ j`, where
`S(k, j) = Nat.stirlingSecond k j` are the Stirling numbers of the second kind. -/
lemma integral_pow_map_cast_poissonMeasure (r : ℝ≥0) (k : ℕ) :
    ∫ x, x ^ k ∂Po(ℝ, r) = ∑ j ∈ Finset.range (k + 1), (Nat.stirlingSecond k j : ℝ) * r ^ j :=
  integral_map_cast_poissonMeasure_of_hasSum (by fun_prop) (hasSum_mul_pow_poissonMeasure r k)

/-- The mean of the Poisson distribution with rate `r` is `r`. -/
lemma integral_id_map_cast_poissonMeasure (r : ℝ≥0) : ∫ x, x ∂Po(ℝ, r) = r := by
  simpa [Finset.sum_range_succ, Nat.stirlingSecond_self] using
    integral_pow_map_cast_poissonMeasure r 1

/-- The second moment of the Poisson distribution with rate `r` is `r ^ 2 + r`. -/
lemma integral_pow_two_map_cast_poissonMeasure (r : ℝ≥0) :
    ∫ x, x ^ 2 ∂Po(ℝ, r) = r ^ 2 + r := by
  rw [integral_pow_map_cast_poissonMeasure]
  simp [Finset.sum_range_succ, Nat.stirlingSecond]
  ring

/-- The third moment of the Poisson distribution with rate `r` is `r ^ 3 + 3 * r ^ 2 + r`. -/
lemma integral_pow_three_map_cast_poissonMeasure (r : ℝ≥0) :
    ∫ x, x ^ 3 ∂Po(ℝ, r) = r ^ 3 + 3 * r ^ 2 + r := by
  rw [integral_pow_map_cast_poissonMeasure]
  simp [Finset.sum_range_succ, Nat.stirlingSecond]
  ring

/-- The fourth moment of the Poisson distribution with rate `r` is
`r ^ 4 + 6 * r ^ 3 + 7 * r ^ 2 + r`. -/
lemma integral_pow_four_map_cast_poissonMeasure (r : ℝ≥0) :
    ∫ x, x ^ 4 ∂Po(ℝ, r) = r ^ 4 + 6 * r ^ 3 + 7 * r ^ 2 + r := by
  rw [integral_pow_map_cast_poissonMeasure]
  simp [Finset.sum_range_succ, Nat.stirlingSecond]
  ring

/-- The variance of the Poisson distribution with rate `r` is `r`. -/
lemma variance_id_map_cast_poissonMeasure (r : ℝ≥0) : Var[id; Po(ℝ, r)] = r := by
  rw [variance_eq_sub (memLp_id_map_cast_poissonMeasure r 2)]
  simp only [Pi.pow_apply, id_eq, integral_pow_two_map_cast_poissonMeasure,
    integral_id_map_cast_poissonMeasure]
  ring

/-- The third central moment of the Poisson distribution with rate `r` is `r`. -/
lemma centralMoment_three_map_cast_poissonMeasure (r : ℝ≥0) :
    centralMoment id 3 Po(ℝ, r) = r := by
  simp only [centralMoment, Pi.pow_apply, Pi.sub_apply, id_eq,
    integral_id_map_cast_poissonMeasure]
  refine integral_map_cast_poissonMeasure_of_hasSum (by fun_prop) ?_
  convert (((hasSum_mul_pow_poissonMeasure r 3).add
    ((hasSum_mul_pow_poissonMeasure r 2).mul_left (-3 * (r : ℝ)))).add
    ((hasSum_mul_pow_poissonMeasure r 1).mul_left (3 * (r : ℝ) ^ 2))).add
    ((hasSum_mul_pow_poissonMeasure r 0).mul_left (-(r : ℝ) ^ 3)) using 1
  · ext n
    ring
  · simp [Finset.sum_range_succ, Nat.stirlingSecond]
    ring

/-- The fourth central moment of the Poisson distribution with rate `r` is `3 * r ^ 2 + r`. -/
lemma centralMoment_four_map_cast_poissonMeasure (r : ℝ≥0) :
    centralMoment id 4 Po(ℝ, r) = 3 * r ^ 2 + r := by
  simp only [centralMoment, Pi.pow_apply, Pi.sub_apply, id_eq,
    integral_id_map_cast_poissonMeasure]
  refine integral_map_cast_poissonMeasure_of_hasSum (by fun_prop) ?_
  convert ((((hasSum_mul_pow_poissonMeasure r 4).add
    ((hasSum_mul_pow_poissonMeasure r 3).mul_left (-4 * (r : ℝ)))).add
    ((hasSum_mul_pow_poissonMeasure r 2).mul_left (6 * (r : ℝ) ^ 2))).add
    ((hasSum_mul_pow_poissonMeasure r 1).mul_left (-4 * (r : ℝ) ^ 3))).add
    ((hasSum_mul_pow_poissonMeasure r 0).mul_left ((r : ℝ) ^ 4)) using 1
  · ext n
    ring
  · simp [Finset.sum_range_succ, Nat.stirlingSecond]
    ring

end ProbabilityTheory
