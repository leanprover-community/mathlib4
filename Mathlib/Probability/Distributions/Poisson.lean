/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Probability.ProbabilityMassFunction.Binomial

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
  have : (fun i ↦ rexp r * (rexp (-r) * r ^ i / Nat.factorial i)) =
      fun i ↦ r ^ i / Nat.factorial i := by
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

lemma poissonPMFReal_ofReal_eq_poissonPMF (r : ℝ≥0) (n : ℕ) :
    ENNReal.ofReal (poissonPMFReal r n) = poissonPMF r n := by
  simpa only [poissonPMF] using by rfl

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

variable {p : ℕ → ℝ} {r : ℝ} (k : ℕ)

lemma tendsto_zero_of_tendsto_mul_atTop (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto p atTop (𝓝 0) := by
  have : (fun n => (n * p n) * (1 / n)) =ᶠ[atTop] p := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    calc
      _ = p n * (n * (1 / n)) := by ac_rfl
      _ = p n := by simp [field]
  simpa using (hr.mul tendsto_one_div_atTop_nhds_zero_nat).congr' this

lemma tendsto_choose_mul_pow_atTop (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => n.choose k * (p n) ^ k) atTop (𝓝 (r ^ k / k.factorial)) := by
  set f : ℕ → ℝ := fun n => n.choose k * (p n) ^ k with hf
  set g : ℕ → ℝ := fun n => ((n * p n) ^ k) / k.factorial with hg
  have hfg : f ~[atTop] g := by
    have h1 : f ~[atTop] (fun n => (n ^ k / k.factorial) * (p n) ^ k) :=
      (isEquivalent_choose k).mul IsEquivalent.refl
    refine h1.congr_right (EventuallyEq.of_eq ?_)
    ext n
    simp [field, mul_pow]
  have hg : Tendsto g atTop (𝓝 (r ^ k / k.factorial)) := by
    simpa [g, div_eq_mul_inv] using (hr.pow k).mul_const ((k.factorial : ℝ)⁻¹)
  simpa [f] using (hfg.tendsto_nhds_iff).2 hg

/-- **Poisson limit Theorem** : Assume `n * p n → r` as `n → ∞`. Then the `k`-th term of the
binomial pmf converges to the `k`-th term of `Poisson r`:

`(n.choose k) * (p n)^k * (1 - p n)^(n - k) → exp (-r) * r^k / k!`.
-/
theorem tendsto_choose_mul_pow_of_tendsto_mul_atTop (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => n.choose k * (p n) ^ k * (1 - p n) ^ (n - k))
    atTop (𝓝 (rexp (-r) * (r ^ k) / k.factorial)) := by
  have h_one_sub_pow : Tendsto (fun n => (1 - p n) ^ (n - k)) atTop (𝓝 (rexp (-r))) :=
    have hneg : Tendsto (fun n => n * (-p n)) atTop (𝓝 (-r)) := by
      simpa [mul_neg] using hr.neg
    have hpow_n : Tendsto (fun n => (1 - p n) ^ n) atTop (𝓝 (rexp (-r))) := by
      simpa [sub_eq_add_neg] using Real.tendsto_one_add_pow_exp_of_tendsto hneg
    have h1 : Tendsto (fun n => 1 - p n) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_zero_of_tendsto_mul_atTop hr)
    have hpow_k : Tendsto (fun n => (1 - p n) ^ k) atTop (𝓝 1) := by
      simpa using h1.pow k
    have hinv_k : Tendsto (fun n => ((1 - p n) ^ k)⁻¹) atTop (𝓝 1) := by
      simpa using (hpow_k.inv₀ (by norm_num))
    have hp_lt_half : ∀ᶠ n in atTop, p n < 1 / 2 :=
      (tendsto_zero_of_tendsto_mul_atTop hr).eventually (Iio_mem_nhds (by norm_num))
    have hone_ne : ∀ᶠ n in atTop, (1 - p n) ≠ 0 := by
      filter_upwards [hp_lt_half] with n hn
      exact ne_of_gt (sub_pos.2 (lt_trans hn (by norm_num)))
    have hEq : (fun n => (1 - p n) ^ (n - k))
          =ᶠ[atTop] (fun n => (1 - p n) ^ n * ((1 - p n) ^ k)⁻¹) := by
      filter_upwards [eventually_ge_atTop k, hone_ne] with n hn hne
      exact pow_sub₀ (1 - p n) hne hn
    have hprod : Tendsto (fun n => (1 - p n) ^ n * ((1 - p n) ^ k)⁻¹) atTop (𝓝 (rexp (-r))) := by
      simpa [mul_assoc] using (hpow_n.mul hinv_k)
    Tendsto.congr' (EventuallyEq.symm hEq) hprod
  simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
    (tendsto_choose_mul_pow_atTop k hr).mul h_one_sub_pow

lemma tendsto_poissonPMFReal_pow_of_tendsto_mul_atTop (r : ℝ≥0)
    (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) : Tendsto
    (fun n => n.choose k * (p n) ^ k * (1 - p n) ^ (n - k)) atTop (𝓝 (poissonPMFReal r k)) :=
  tendsto_choose_mul_pow_of_tendsto_mul_atTop k hr

open ENNReal in
lemma PMFbinomial_tendsto_poissonPMFReal_atTop (r : ℝ≥0) (p : ℕ → ℝ≥0) (h : ∀ n, p n ≤ 1)
    (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) : Tendsto (fun n ↦ PMF.binomial (p n) (h n) n
    (Fin.ofNat (n + 1) k)) atTop (𝓝 (poissonPMF r k)) := by
  have t1 : Tendsto (fun n => (ENNReal.ofReal (n.choose k * (p n) ^ k * (1 - p n) ^ (n - k) : ℝ)))
    atTop (𝓝 (ENNReal.ofReal (poissonPMFReal r k))) :=
    tendsto_ofReal (tendsto_poissonPMFReal_pow_of_tendsto_mul_atTop k r (by norm_cast))
  rw [poissonPMFReal_ofReal_eq_poissonPMF r k] at t1
  refine Tendsto.congr' ?_ t1
  simp only [PMF.binomial_apply, EventuallyEq, Fin.ofNat_eq_cast, Fin.val_natCast, Fin.val_last,
    eventually_atTop, ge_iff_le]
  use k
  intro b hb
  set x : ℝ := NNReal.toReal (p b) with hx
  have eq0 : k % (b + 1) = k := by simpa using Order.lt_add_one_iff.mpr hb
  have eq1 : 1 - (p b : ℝ≥0∞) = ENNReal.ofReal (1 - x : ℝ) := by norm_cast
  have : 1 - x ≥ 0 := by simp [hx, h b]
  rw [eq0, eq1, coe_nnreal_eq (p b), mul_rotate (↑(b.choose k)) (x ^ k) ((1 - x) ^ (b - k)),
    ofReal_mul, ENNReal.ofReal_mul, ofReal_pow, ofReal_pow, ofReal_natCast]
  repeat positivity

end ProbabilityTheory
