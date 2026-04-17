/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Binomial

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.ComplexMGF

/-!
# Poisson limit of binomial probabilities

This file proves a Poisson limit theorem.

Fix `k : ℕ`. Assuming `n * p n → r` as `n → ∞`, we show
`PMF.binomial (p n) (h n) n (Fin.ofNat (n + 1) k) → poissonPMF r k`.

## Main results

* `ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop`:
  if `n * p n → r`, then `n.choose k * (p n)^k * (1 - p n)^(n - k) → exp (-r) * r^k / k!`.

* `ProbabilityTheory.binomial_tendsto_poissonPMFReal_atTop`:
  convergence of `PMF.binomial` to `poissonPMF` in `ℝ≥0∞` under the natural hypotheses
  (`p n ≤ 1` and `n * p n → r`).

## Tags

binomial distribution, Poisson distribution, asymptotics, limits, probability mass function
-/

public section

namespace ProbabilityTheory

open scoped NNReal

open Filter Topology ENNReal

variable {p : ℕ → ℝ} {r : ℝ} (k : ℕ)

lemma tendsto_zero_of_tendsto_mul_atTop (hr : Tendsto (fun n ↦ n * p n) atTop (𝓝 r)) :
    Tendsto p atTop (𝓝 0) := by
  have : (fun n ↦ (n * p n) * (1 / n)) =ᶠ[atTop] p := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    field
  simpa using (hr.mul tendsto_one_div_atTop_nhds_zero_nat).congr' this

open Asymptotics in
lemma tendsto_choose_mul_pow_atTop (hr : Tendsto (fun n ↦ n * p n) atTop (𝓝 r)) :
    Tendsto (fun n ↦ n.choose k * (p n) ^ k) atTop (𝓝 (r ^ k / k.factorial)) := by
  have : (fun n ↦ n.choose k * (p n) ^ k) ~[atTop] (fun n ↦ ((n * p n) ^ k) / k.factorial) :=
    calc
    _ ~[atTop] (fun n ↦ (n ^ k / k.factorial) * (p n) ^ k) :=
      (isEquivalent_choose k).mul IsEquivalent.refl
    _ ~[atTop] (fun n ↦ ((n * p n) ^ k) / k.factorial) :=
      EventuallyEq.isEquivalent (.of_eq (by ext; field))
  refine (IsEquivalent.tendsto_nhds_iff this).mpr ?_
  simpa [div_eq_mul_inv] using (hr.pow k).mul_const ((k.factorial : ℝ)⁻¹)

/--
**Poisson limit Theorem**: If `n * p n → r` as `n → ∞`. Then
`(n.choose k) * (p n)^k * (1 - p n)^(n - k) → exp (-r) * r^k / k!`.
-/
theorem tendsto_choose_mul_pow_of_tendsto_mul_atTop (hr : Tendsto (fun n ↦ n * p n) atTop (𝓝 r)) :
    Tendsto (fun n ↦ n.choose k * (p n) ^ k * (1 - p n) ^ (n - k))
    atTop (𝓝 (Real.exp (-r) * (r ^ k) / k.factorial)) := by
  rw [mul_div_assoc, mul_comm]
  refine (tendsto_choose_mul_pow_atTop k hr).mul ?_
  have hp_lt_half : ∀ᶠ n in atTop, p n < 1 / 2 :=
    (tendsto_zero_of_tendsto_mul_atTop hr).eventually (Iio_mem_nhds (by norm_num))
  have hEq : (fun n ↦ (1 - p n) ^ (n - k)) =ᶠ[atTop]
      (fun n ↦ (1 - p n) ^ n * ((1 - p n) ^ k)⁻¹) := by
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
Another version of Poisson Limit Theorem: convergence of `PMF.binomial` to `poissonPMF` in `ℝ≥0∞`
under the natural hypotheses (`∀ n, p n ≤ 1` and `r ≥ 0`).
-/
lemma binomial_tendsto_poissonPMFReal_atTop {r : ℝ≥0} {p : ℕ → ℝ≥0} (h : ∀ n, p n ≤ 1)
    (hr : Tendsto (fun n ↦ n * p n) atTop (𝓝 r)) :
    Tendsto (fun n ↦ PMF.binomial (p n) (h n) n (Fin.ofNat (n + 1) k))
    atTop (𝓝 (poissonMeasure r {k})) := by
  have t1 : Tendsto (fun n ↦ (ENNReal.ofReal (n.choose k * (p n) ^ k * (1 - p n) ^ (n - k) : ℝ)))
      atTop (𝓝 (poissonMeasure r {k})) := by
    simp_rw [poissonMeasure_singleton]
    exact tendsto_ofReal (tendsto_choose_mul_pow_of_tendsto_mul_atTop k (by norm_cast))
  refine Tendsto.congr' ?_ t1
  simpa only [EventuallyEq, eventually_atTop, ge_iff_le] using
    ⟨k, fun b hb ↦ PMF.binomial_apply_of_le hb (h b)⟩

section PoissonStructure

open MeasureTheory Complex Real

lemma complexMGF_id_poissonMeasure_map_natCast (r : ℝ≥0) (z : ℂ) :
    complexMGF id ((poissonMeasure r).map (fun n : ℕ ↦ (n : ℝ))) z =
    cexp ((r : ℂ) * (cexp z - 1)) := by
  rw [complexMGF, integral_map
      (Measurable.aemeasurable (Measurable.of_discrete (f := fun n : ℕ ↦ (n : ℝ))))
      (by fun_prop)]
  rw [integral_poissonMeasure]
  change ∑' n : ℕ, (rexp (-r) * r ^ n / n.factorial) • cexp (z * n) = _
  have hsum : HasSum (fun n : ℕ ↦ (rexp (-r) * r ^ n / n.factorial * cexp (z * n)))
      (rexp (-r) * cexp (r * cexp z)) := by
    have hsum := (NormedSpace.expSeries_div_hasSum_exp (r * cexp z)).mul_left (rexp (-r) : ℂ)
    convert hsum using 1
    · funext n
      rw [CommMonoid.mul_comm z n, Complex.exp_nat_mul]
      simp [mul_assoc, mul_left_comm, mul_comm, mul_pow, div_eq_mul_inv]
    · rw [Complex.exp_eq_exp_ℂ]
  have htsum : ∑' n : ℕ, (rexp (-r) * r ^ n / n.factorial) • cexp (z * n) =
      rexp (-r) * cexp (r * cexp z) := by
    simpa [smul_eq_mul] using hsum.tsum_eq
  rw [htsum]
  simp [← Complex.exp_add]
  congr 1
  ring

lemma mgf_id_poissonMeasure_map_natCast (r : ℝ≥0) (t : ℝ) :
    mgf id ((poissonMeasure r).map (fun n : ℕ ↦ (n : ℝ))) t = rexp (r * (rexp t - 1)) := by
  have h := complexMGF_id_poissonMeasure_map_natCast r (t : ℂ)
  rw [complexMGF_ofReal] at h
  exact ofReal_injective <| by simpa [ofReal_exp, Complex.ofReal_mul, Complex.ofReal_sub] using h

lemma charFun_poissonMeasure_map_natCast (r : ℝ≥0) (t : ℝ) :
    charFun ((poissonMeasure r).map (fun n : ℕ ↦ (n : ℝ))) t =
      cexp (r * (cexp (t * I) - 1)) := by
  simpa [complexMGF_id_mul_I] using complexMGF_id_poissonMeasure_map_natCast r (t * I)

lemma poissonMeasure_conv (r s : ℝ≥0) :
    poissonMeasure r ∗ poissonMeasure s = poissonMeasure (r + s) := by
  apply (MeasurableEmbedding.natCast (α := ℝ)).map_injective
  apply MeasureTheory.Measure.ext_of_charFun
  ext t
  change charFun (Measure.map (⇑(Nat.castAddMonoidHom ℝ)) (poissonMeasure r ∗ poissonMeasure s)) t =
    charFun (Measure.map (⇑(Nat.castAddMonoidHom ℝ)) (poissonMeasure (r + s))) t
  rw [Measure.map_conv_addMonoidHom (Nat.castAddMonoidHom ℝ) (by fun_prop)]
  calc
    _ = charFun (Measure.map (⇑(Nat.castAddMonoidHom ℝ)) (poissonMeasure r)) t *
        charFun (Measure.map (⇑(Nat.castAddMonoidHom ℝ)) (poissonMeasure s)) t := by
      rw [charFun_conv]
    _ = cexp (r * (cexp (t * I) - 1)) * cexp ((s : ℂ) * (cexp (t * I) - 1)) :=
      congrArg₂ (fun a b : ℂ ↦ a * b) (charFun_poissonMeasure_map_natCast r t)
        (charFun_poissonMeasure_map_natCast s t)
    _ = cexp ((r + s) * (cexp (t * I) - 1)) := by
      rw [← Complex.exp_add]
      congr 1
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm, mul_add]
    _ = charFun (Measure.map (⇑(Nat.castAddMonoidHom ℝ)) (poissonMeasure (r + s))) t := by
      simpa using (charFun_poissonMeasure_map_natCast (r + s) t).symm

lemma IndepFun.hasLaw_add_poissonMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X Y : Ω → ℕ} (r s : ℝ≥0)
    (hX : HasLaw X (poissonMeasure r) P) (hY : HasLaw Y (poissonMeasure s) P) (hXY : X ⟂ᵢ[P] Y) :
    HasLaw (fun ω ↦ X ω + Y ω) (poissonMeasure (r + s)) P := by
  simpa [poissonMeasure_conv] using hXY.hasLaw_add hX hY

end PoissonStructure

end ProbabilityTheory
