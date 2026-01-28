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
    calc
      _ = p n * (n * (1 / n)) := by ac_rfl
      _ = p n := by simp [field]
  simpa using (hr.mul tendsto_one_div_atTop_nhds_zero_nat).congr' this

open Asymptotics in
lemma tendsto_choose_mul_pow_atTop (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => n.choose k * (p n) ^ k) atTop (𝓝 (r ^ k / k.factorial)) :=
  let f : ℕ → ℝ := fun n => n.choose k * (p n) ^ k
  let g : ℕ → ℝ := fun n => ((n * p n) ^ k) / k.factorial
  have hfg : f ~[atTop] g := by
    have h1 : f ~[atTop] (fun n => (n ^ k / k.factorial) * (p n) ^ k) :=
      (isEquivalent_choose k).mul IsEquivalent.refl
    refine h1.congr_right (EventuallyEq.of_eq ?_)
    ext n
    simp [field, mul_pow]
  have hg : Tendsto g atTop (𝓝 (r ^ k / k.factorial)) := by
    simpa [g, div_eq_mul_inv] using (hr.pow k).mul_const ((k.factorial : ℝ)⁻¹)
  (IsEquivalent.tendsto_nhds_iff hfg).mpr hg

/--
**Poisson limit Theorem** : If `n * p n → r` as `n → ∞`. Then
`(n.choose k) * (p n)^k * (1 - p n)^(n - k) → exp (-r) * r^k / k!`.
-/
theorem tendsto_choose_mul_pow_of_tendsto_mul_atTop (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => n.choose k * (p n) ^ k * (1 - p n) ^ (n - k))
    atTop (𝓝 (Real.exp (-r) * (r ^ k) / k.factorial)) := by
  have h_one_sub_pow : Tendsto (fun n => (1 - p n) ^ (n - k)) atTop (𝓝 (Real.exp (-r))) := by
    have hneg : Tendsto (fun n => n * (-p n)) atTop (𝓝 (-r)) := by
      simpa [mul_neg] using hr.neg
    have hpow_n : Tendsto (fun n => (1 - p n) ^ n) atTop (𝓝 (Real.exp (-r))) := by
      simpa [sub_eq_add_neg] using Real.tendsto_one_add_pow_exp_of_tendsto hneg
    have h1 : Tendsto (fun n => 1 - p n) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_zero_of_tendsto_mul_atTop hr)
    have hinv_k : Tendsto (fun n => ((1 - p n) ^ k)⁻¹) atTop (𝓝 1) := by
      simpa only [one_pow, inv_one] using (h1.pow k).inv₀ (by norm_num)
    have hp_lt_half : ∀ᶠ n in atTop, p n < 1 / 2 :=
      (tendsto_zero_of_tendsto_mul_atTop hr).eventually (Iio_mem_nhds (by norm_num))
    have hEq : (fun n => (1 - p n) ^ (n - k))
          =ᶠ[atTop] (fun n => (1 - p n) ^ n * ((1 - p n) ^ k)⁻¹) := by
      filter_upwards [eventually_ge_atTop k, hp_lt_half] with n hn hne
      rw [pow_sub₀ _ (by linarith) hn]
    have : Tendsto (fun n => (1 - p n) ^ n * ((1 - p n) ^ k)⁻¹) atTop (𝓝 (Real.exp (-r))) := by
      simpa [mul_assoc] using (hpow_n.mul hinv_k)
    exact Tendsto.congr' (EventuallyEq.symm hEq) this
  simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
    (tendsto_choose_mul_pow_atTop k hr).mul h_one_sub_pow

/--
Another version of Possion Limit Theorem : using `poissonPMFReal` (with `r : ℝ≥0`).
-/
lemma tendsto_poissonPMFReal_pow_of_tendsto_mul_atTop (r : ℝ≥0)
    (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) : Tendsto
    (fun n => n.choose k * (p n) ^ k * (1 - p n) ^ (n - k)) atTop (𝓝 (poissonPMFReal r k)) :=
  tendsto_choose_mul_pow_of_tendsto_mul_atTop k hr

/--
Another version of Possion Limit Theorem : convergence of `PMF.binomial` to `poissonPMF` in `ℝ≥0∞`
under the natural hypotheses (`∀ n, p n ≤ 1` and `r ≥ 0`).
-/
lemma PMFbinomial_tendsto_poissonPMFReal_atTop {r : ℝ≥0} {p : ℕ → ℝ≥0} (h : ∀ n, p n ≤ 1)
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
  rw [eq0, eq1, coe_nnreal_eq (p b), mul_rotate ((b.choose k : ℝ)) (x ^ k) ((1 - x) ^ (b - k)),
    ofReal_mul, ENNReal.ofReal_mul, ofReal_pow, ofReal_pow, ofReal_natCast]
  repeat positivity

end ProbabilityTheory
