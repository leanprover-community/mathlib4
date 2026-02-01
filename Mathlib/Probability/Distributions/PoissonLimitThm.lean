/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Probability.Distributions.Poisson
public import Mathlib.Probability.ProbabilityMassFunction.Binomial

/-!
# Poisson limit of binomial probabilities

This file proves a Poisson limit theorem.

Fix `k : ℕ`. Assuming `n * p n → r` as `n → ∞`, we show
`PMF.binomial (p n) (h n) n (Fin.ofNat (n + 1) k) → poissonPMF r k`.

## Main results

* `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`:
  if `n * p n → r`, then `n.choose k * (p n)^k * (1 - p n)^(n - k) → exp (-r) * r^k / k!`.

* `ProbabilityTheory.tendsto_poissonPMFReal_pow_of_tendsto_mul_atTop`:
  the same limit rewritten using `poissonPMFReal` (with `r : ℝ≥0`).

* `ProbabilityTheory.PMFbinomial_tendsto_poissonPMFReal_atTop`:
  convergence of `PMF.binomial` to `poissonPMF` in `ℝ≥0∞` under the natural hypotheses
  (`p n ≤ 1` and `n * p n → r`).

## Tags

binomial distribution, Poisson distribution, asymptotics, limits, probability mass function
-/

@[expose] public section

namespace ProbabilityTheory

open scoped NNReal

open Filter Topology ENNReal

variable {p : ℕ → ℝ} {r : ℝ} (k : ℕ)

lemma tendsto_zero_of_tendsto_mul_atTop (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto p atTop (𝓝 0) := by
  have : (fun n => (n * p n) * (1 / n)) =ᶠ[atTop] p := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    field
  simpa using (hr.mul tendsto_one_div_atTop_nhds_zero_nat).congr' this

open Asymptotics in
lemma tendsto_choose_mul_pow_atTop (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => n.choose k * (p n) ^ k) atTop (𝓝 (r ^ k / k.factorial)) := by
  have : (fun n => n.choose k * (p n) ^ k) ~[atTop] (fun n ↦ ((n * p n) ^ k) / k.factorial) :=
    calc
    _ ~[atTop] (fun n => (n ^ k / k.factorial) * (p n) ^ k) :=
      (isEquivalent_choose k).mul IsEquivalent.refl
    _ ~[atTop] (fun n ↦ ((n * p n) ^ k) / k.factorial) :=
      EventuallyEq.isEquivalent (.of_eq (by ext; field))
  refine (IsEquivalent.tendsto_nhds_iff this).mpr ?_
  simpa [div_eq_mul_inv] using (hr.pow k).mul_const ((k.factorial : ℝ)⁻¹)

/--
**Poisson limit Theorem**: If `n * p n → r` as `n → ∞`. Then
`(n.choose k) * (p n)^k * (1 - p n)^(n - k) → exp (-r) * r^k / k!`.
-/
theorem tendsto_choose_mul_pow_of_tendsto_mul_atTop (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => n.choose k * (p n) ^ k * (1 - p n) ^ (n - k))
    atTop (𝓝 (Real.exp (-r) * (r ^ k) / k.factorial)) := by
  rw [mul_div_assoc, mul_comm]
  refine (tendsto_choose_mul_pow_atTop k hr).mul ?_
  have hp_lt_half : ∀ᶠ n in atTop, p n < 1 / 2 :=
    (tendsto_zero_of_tendsto_mul_atTop hr).eventually (Iio_mem_nhds (by norm_num))
  have hEq : (fun n => (1 - p n) ^ (n - k))
        =ᶠ[atTop] (fun n => (1 - p n) ^ n * ((1 - p n) ^ k)⁻¹) := by
    filter_upwards [eventually_ge_atTop k, hp_lt_half] with n hn hne
    rw [pow_sub₀ _ (by grind) hn]
  refine Tendsto.congr' hEq.symm ?_
  have : Real.exp (-r) = Real.exp (-r) * (1 ^ k)⁻¹ := by field
  rw [this]
  refine Tendsto.mul (Real.tendsto_one_add_pow_exp_of_tendsto ?_) ?_
  · simpa using hr.neg
  refine Tendsto.inv₀ (.pow ?_ k) (by simp)
  · simpa using tendsto_const_nhds.sub (tendsto_zero_of_tendsto_mul_atTop hr)

/--
Another version of Possion Limit Theorem: convergence of `PMF.binomial` to `poissonPMF` in `ℝ≥0∞`
under the natural hypotheses (`∀ n, p n ≤ 1` and `r ≥ 0`).
-/
lemma PMFbinomial_tendsto_poissonPMFReal_atTop {r : ℝ≥0} {p : ℕ → ℝ≥0} (h : ∀ n, p n ≤ 1)
    (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) : Tendsto (fun n ↦ PMF.binomial (p n) (h n) n
    (Fin.ofNat (n + 1) k)) atTop (𝓝 (poissonPMF r k)) := by
  have t1 : Tendsto (fun n => (ENNReal.ofReal (n.choose k * (p n) ^ k * (1 - p n) ^ (n - k) : ℝ)))
    atTop (𝓝 (ENNReal.ofReal (poissonPMFReal r k))) :=
    tendsto_ofReal (tendsto_choose_mul_pow_of_tendsto_mul_atTop k (by norm_cast))
  rw [poissonPMFReal_ofReal_eq_poissonPMF r k] at t1
  refine Tendsto.congr' ?_ t1
  simpa only [EventuallyEq, eventually_atTop, ge_iff_le] using
    ⟨k, fun b hb ↦ PMF.binomial_apply_of_le hb (h b)⟩

end ProbabilityTheory
