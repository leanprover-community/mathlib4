/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

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
@[fun_prop]
lemma measurable_poissonPMFReal (r : ℝ≥0) : Measurable (poissonPMFReal r) := by fun_prop

@[fun_prop]
lemma stronglyMeasurable_poissonPMFReal (r : ℝ≥0) : StronglyMeasurable (poissonPMFReal r) :=
  stronglyMeasurable_iff_measurable.mpr (measurable_poissonPMFReal r)

end PoissonPMF

/-- Measure defined by the Poisson distribution -/
noncomputable
def poissonMeasure (r : ℝ≥0) : Measure ℕ := (poissonPMF r).toMeasure

instance isProbabilityMeasurePoisson (r : ℝ≥0) :
    IsProbabilityMeasure (poissonMeasure r) := PMF.toMeasure.isProbabilityMeasure (poissonPMF r)

open Asymptotics

variable (p : ℕ → ℝ) (lam : ℝ) (k : ℕ)
    (hp01 : ∀ n, p n ∈ Set.Icc (0 : ℝ) 1)
    (hlam : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 lam))

lemma hp0 (hlam : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 lam)) :
    Tendsto p atTop (𝓝 (0 : ℝ)) := by
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hmul : Tendsto (fun n : ℕ => ((n : ℝ) * p n) * ((1 : ℝ) / (n : ℝ))) atTop (𝓝 (lam * 0)) :=
    hlam.mul hinv
  have hEq : (fun n : ℕ => ((n : ℝ) * p n) * ((1 : ℝ) / (n : ℝ))) =ᶠ[atTop] p := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    calc
      _ = p n * ((n : ℝ) * ((1 : ℝ) / (n : ℝ))) := by ac_rfl
      _ = p n := by simp [field]
  simpa using hmul.congr' hEq

lemma h_choose_mul_pk (hlam : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 lam)) :
      Tendsto (fun n : ℕ => ((n.choose k : ℕ) : ℝ) * (p n) ^ k)
        atTop (𝓝 (lam ^ k / (k.factorial : ℝ))) := by
  have hchoose_equiv :
      (fun n : ℕ => ((n.choose k : ℕ) : ℝ))
        ~[atTop] (fun n : ℕ => (n : ℝ) ^ k / (k.factorial : ℝ)) := by
    simpa using (isEquivalent_choose k)
  set f : ℕ → ℝ := fun n => ((n.choose k : ℕ) : ℝ) * (p n) ^ k with hf
  set g : ℕ → ℝ := fun n => (((n : ℝ) * p n) ^ k) / (k.factorial : ℝ) with hg
  have hfg : f ~[atTop] g := by
    have h1 : f ~[atTop] (fun n : ℕ => ((n : ℝ) ^ k / (k.factorial : ℝ)) * (p n) ^ k) :=
      hchoose_equiv.mul IsEquivalent.refl
    refine h1.congr_right ?_
    have : (fun n ↦ ↑n ^ k / ↑k.factorial * p n ^ k)
          = fun n ↦ (↑n * p n) ^ k / ↑k.factorial := by
      ext n
      simp [field, mul_pow]
    simp [hg, this]
  have hg : Tendsto g atTop (𝓝 (lam ^ k / (k.factorial : ℝ))) := by
    simpa [g, div_eq_mul_inv] using (hlam.pow k).mul_const ((k.factorial : ℝ)⁻¹)
  simpa [f] using (hfg.tendsto_nhds_iff).2 hg

theorem poisson_limit (hlam : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 lam)) :
    Tendsto (fun n : ℕ => ((n.choose k : ℕ) : ℝ) * (p n) ^ k * (1 - p n) ^ (n - k))
    atTop (𝓝 (Real.exp (-lam) * (lam ^ k) / (k.factorial : ℝ))) := by
  have h_one_sub_pow : Tendsto (fun n : ℕ => (1 - p n) ^ (n - k)) atTop (𝓝 (Real.exp (-lam))) := by
    have hneg : Tendsto (fun n : ℕ => (n : ℝ) * (-p n)) atTop (𝓝 (-lam)) := by
      simpa [mul_neg] using hlam.neg
    have hpow_n : Tendsto (fun n : ℕ => (1 - p n) ^ n) atTop (𝓝 (Real.exp (-lam))) := by
      simpa [sub_eq_add_neg] using Real.tendsto_one_add_pow_exp_of_tendsto hneg
    have h1 : Tendsto (fun n : ℕ => 1 - p n) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub (hp0 p lam hlam)
    have hpow_k : Tendsto (fun n : ℕ => (1 - p n) ^ k) atTop (𝓝 (1 : ℝ)) := by
      simpa using h1.pow k
    have hinv_k : Tendsto (fun n : ℕ => ((1 - p n) ^ k)⁻¹) atTop (𝓝 (1 : ℝ)) := by
      simpa using (hpow_k.inv₀ (by norm_num : (1 : ℝ) ≠ 0))
    have hp_lt_half : ∀ᶠ n in atTop, p n < (1 / 2 : ℝ) :=
      (hp0 p lam hlam).eventually (Iio_mem_nhds (by norm_num))
    have hone_ne : ∀ᶠ n in atTop, (1 - p n) ≠ 0 := by
      filter_upwards [hp_lt_half] with n hn
      exact ne_of_gt (sub_pos.2 (lt_trans hn (by norm_num)))
    have hk_le : ∀ᶠ n in atTop, k ≤ n := eventually_ge_atTop k
    have hEq : (fun n : ℕ => (1 - p n) ^ (n - k))
          =ᶠ[atTop] (fun n : ℕ => (1 - p n) ^ n * ((1 - p n) ^ k)⁻¹) := by
      filter_upwards [hk_le, hone_ne] with n hn hne
      simpa using (pow_sub₀ (a := (1 - p n)) hne hn)
    have hprod : Tendsto (fun n : ℕ => (1 - p n) ^ n * ((1 - p n) ^ k)⁻¹)
          atTop (𝓝 (Real.exp (-lam))) := by
      simpa [mul_assoc] using (hpow_n.mul hinv_k)
    simpa using (hprod.congr' hEq.symm)
  simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
    (h_choose_mul_pk p lam k hlam).mul h_one_sub_pow

lemma _PMF (hpos : lam ≥ 0)
    (hlam : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 lam)) :
    Tendsto (fun n : ℕ => ((n.choose k : ℕ) : ℝ) * (p n) ^ k * (1 - p n) ^ (n - k))
    atTop (𝓝 (ProbabilityTheory.poissonPMFReal ⟨lam, by simp [hpos]⟩ k)) := by
  dsimp [poissonPMFReal]
  exact poisson_limit p lam k hlam

end ProbabilityTheory
