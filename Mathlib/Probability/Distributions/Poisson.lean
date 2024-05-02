/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/

import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.NormedSpace.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Probability.Notation
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Binomial

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

open BigOperators MeasureTheory PMF Real Set Filter Topology

namespace ProbabilityTheory

section PoissonPMF

/-- The pmf of the Poisson distribution depending on its rate, as a function to ℝ -/
noncomputable
def poissonPMFReal (r : ℝ≥0) (n : ℕ) : ℝ := exp (- r) * r ^ n / n !

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

lemma poisson_convolution (r s : ℝ≥0) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), poissonPMFReal r k * poissonPMFReal s (n - k)
    = poissonPMFReal (r + s) n := by
  let K := Finset.range (n + 1)
  have finset_rfl : K = K := by rfl

  /- Case `n = 0` reduces to `exp(-(r + s)) = exp(-r) * exp(-s)`. -/
  by_cases n_zero : n = 0
  · simp [n_zero, poissonPMFReal, exp_add, mul_comm]

  /- Case `r + s = 0` and `n ≠ 0` reduces to `0 = 0`. -/
  by_cases r_plus_s : r + s = 0
  · have r_le_zero : r ≤ 0 := by
      calc
        r ≤ r + s := le_self_add
        _ = 0 := by rw [r_plus_s]
    have r_eq_zero : r = 0 := nonpos_iff_eq_zero.mp r_le_zero
    have s_eq_zero : s = 0 := by
      calc
        s = r + s - r := (add_tsub_cancel_left r s).symm
        _ = 0 := by rw [r_plus_s, r_eq_zero]; simp

    /- Mean-zero Poisson distribution puts all its mass at zero, and is zero everywhere else. -/
    have mean_zero_poisson_pmf (k : ℕ): k ≠ 0 → poissonPMFReal 0 k = 0 := by
      intro k_ne_zero
      unfold poissonPMFReal
      simp [k_ne_zero]

    have : ∀ k ∈ K, poissonPMFReal r k * poissonPMFReal s (n - k) = 0 := by
      intro k k_in
      rw [r_eq_zero, s_eq_zero]
      apply mul_eq_zero.mpr
      by_cases k_zero : k = 0
      · right
        simp [k_zero]
        apply mean_zero_poisson_pmf n n_zero
      · left
        apply mean_zero_poisson_pmf k k_zero

    rw [Finset.sum_congr finset_rfl this, Finset.sum_const_zero, poissonPMFReal, r_plus_s]
    simp [zero_pow, n_zero]


  /- Can now assume `n ≠ 0` and `r + s ≠ 0`. -/
  have expr_pos : rexp r > 0 := exp_pos r
  have exps_pos : rexp s > 0 := exp_pos s
  let p : ℝ≥0 := r / (r + s)
  let p' : ℝ≥0 := p
  have p_le_one : p ≤ 1 := by
    dsimp [p]
    have nonneg : 0 ≤ r + s := zero_le (r + s)
    have h_le : r ≤ r + s := le_self_add
    exact div_le_one_of_le h_le nonneg

  /- Need this as an argument of `binomial`. -/
  have p_le_one' : ENNReal.ofNNReal p ≤ 1 := ENNReal.coe_le_one_iff.mpr p_le_one

  /- I'd like to use this in `simp` later, but it doesn't work. -/
  have one_minus_p : 1 - p = s / (r + s) := by
    calc
      1 - p = 1 - r / (r + s) := by dsimp [p]
      _ = (r + s) / (r + s) - r / (r + s) := by
        have : (r + s) / (r + s) = 1 := by apply (div_eq_one_iff_eq r_plus_s).mpr; rfl
        rw [this]
      _ = (r + s - r) / (r + s) := (NNReal.sub_div (r + s) r (r + s)).symm
      _ = s / (r + s) := by simp

  let binomial_summand (k : ℕ) := (binomial ↑p p_le_one' n k).toReal


  have summand_eq : ∀ k ∈ K, poissonPMFReal r k * poissonPMFReal s (n - k) =
      (poissonPMFReal (r + s) n) * (binomial_summand k) := by
    intro k hk
    have k_le_n : k ≤ n := by
      have : k < n + 1 := List.mem_range.mp hk
      exact Nat.le_of_lt_succ this
    have zero_le_k : 0 ≤ k := by exact Nat.zero_le k
    have n_sub_k_mem_k : (n - k) ∈ K := by
      have : n - k < n + 1 := Nat.sub_lt_succ n k
      exact Finset.mem_range.mpr this

    /- The `dsimp [binomial]` below introduces `k % (n + 1)` for some reason,
    likely because `k` has type `ℕ` and cannot be guaranteed to be bounded by `n + 1` a priori.
    Would appreciate a cleaner way to deal with this. -/
    have remainder (i : ℕ) : i ∈ K → i % (n + 1) = i := by
      intro hik
      rw [Nat.mod_eq]
      simp
      intro hfalse
      have : i < n + 1 := List.mem_range.mp hik
      linarith
    have remainder_k : k % (n + 1) = k := remainder k hk
    -- have : (↑r + ↑s) ^ n / ↑n ! * ↑p ^ k * (1 - ↑p) ^ (n - k) = r ^ k * s ^ (n - k) := sorry
    dsimp [poissonPMFReal, binomial_summand, binomial]
    rw [remainder k hk, Nat.choose_eq_factorial_div_factorial k_le_n, mul_div_assoc]
    symm

    /-I have all the ingredients with `p` and `one_minus_p`, but the coercions seem
    to make it difficult to get `simp` or `ring` to work. I tried writing a `calc`
    block to break it down, but again the coercions were problematic.-/
    sorry


  have binomial_pmf_hassum_one :
      ∑ k ∈ K, binomial_summand k = 1 := by
    dsimp [binomial_summand, binomial]
    have : HasSum (↑(binomial (↑p) p_le_one' n)) 1 := (binomial ↑p p_le_one' n).2
    rw [binomial] at this
    /-I'm having trouble converting `HasSum f 1` into `∑ k ∈ K, f k = 1`.-/
    sorry


  rw [
    Finset.sum_congr finset_rfl summand_eq,
    ← Finset.mul_sum K binomial_summand (poissonPMFReal (r + s) n),
    binomial_pmf_hassum_one
  ]
  simp


/-- The Poisson pmf is measurable. -/
@[measurability]
lemma measurable_poissonPMFReal (r : ℝ≥0) : Measurable (poissonPMFReal r) := by measurability

@[measurability]
lemma stronglyMeasurable_poissonPMFReal (r : ℝ≥0) : StronglyMeasurable (poissonPMFReal r) :=
  stronglyMeasurable_iff_measurable.mpr (measurable_poissonPMFReal r)

end PoissonPMF

/-- Measure defined by the Poisson distribution -/
noncomputable
def poissonMeasure (r : ℝ≥0) : Measure ℕ := (poissonPMF r).toMeasure

instance isProbabilityMeasurePoisson (r : ℝ≥0) :
    IsProbabilityMeasure (poissonMeasure r) := PMF.toMeasure.isProbabilityMeasure (poissonPMF r)

end ProbabilityTheory
