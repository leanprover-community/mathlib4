/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Distributions.Binomial

import Mathlib.MeasureTheory.MeasurableSpace.NCard
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.Independence.InfinitePi

/-!
# The de Moivre–Laplace theorem

We show that the binomial distribution is the law of a sum of independent Bernoulli random
variables, and deduce from the central limit theorem that the standardized binomial distribution
converges to the standard Gaussian.

## Main statements

* `ProbabilityTheory.hasLaw_sum_of_iIndepFun_bernoulli`: the sum of `n` independent
  `p`-Bernoulli random variables with values in `{1, 0}` has law `Bin(n, p)`.
* `ProbabilityTheory.tendstoInDistribution_binomial`: **de Moivre–Laplace theorem**, for
  `0 < p < 1`, `(Bin(n, p) - n p) / √(n p (1 - p))` converges in distribution to
  `gaussianReal 0 1`.
* `ProbabilityTheory.tendsto_binomial_real_setOf_le`: the same statement in terms of cumulative
  distribution functions.

## Tags

central limit theorem, binomial distribution
-/

public section

open MeasureTheory Filter Topology Set
open scoped unitInterval ProbabilityTheory NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {p : I}

lemma infinitePi_bernoulliMeasure_map_sum (n : ℕ) :
    (Measure.infinitePi fun _ : ℕ ↦ Ber((1 : ℝ), 0, p)).map
      (fun x ↦ ∑ k ∈ Finset.range n, x k) = Bin(ℝ, n, p) := by
  classical
  have h₁ : Measure.infinitePi (fun _ : ℕ ↦ Ber((1 : ℝ), 0, p)) =
      (Measure.infinitePi fun _ : ℕ ↦ Ber(True, False, p)).map
        fun ω i ↦ if ω i then (1 : ℝ) else 0 := by
    rw [Measure.infinitePi_map_pi (f := fun (_ : ℕ) (b : Prop) ↦ if b then (1 : ℝ) else 0) _
      fun _ ↦ .of_discrete]
    congr 1
    funext i
    simp [map_bernoulliMeasure]
  have h₂ : setBer(Iio n, p) = ((Measure.infinitePi fun _ : ℕ ↦ Ber(True, False, p)).map
      fun ω i ↦ i ∈ Iio n ∧ ω i).map fun q ↦ {i | q i} := by
    rw [setBernoulli_eq_map, Measure.infinitePi_map_pi (f := fun i b ↦ i ∈ Iio n ∧ b) _
      fun _ ↦ .of_discrete]
    congr 2
    funext i
    rw [map_bernoulliMeasure]
    simp [bernoulliMeasure_def]
  have hm : Measurable fun (ω : ℕ → Prop) (i : ℕ) ↦ if ω i then (1 : ℝ) else 0 :=
    Measurable.of_eval fun i ↦ (Measurable.of_discrete (f := fun b : Prop ↦
      if b then (1 : ℝ) else 0)).comp (measurable_pi_apply i)
  rw [binomial, h₂, h₁, Measure.map_map (by fun_prop) hm,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext ω
  have : {i | i ∈ Iio n ∧ ω i} = ↑((Finset.range n).filter fun i ↦ ω i) := by
    ext i
    simp
  simp only [Function.comp_apply]
  rw [this, Set.ncard_coe_finset]
  simp [Finset.sum_boole]

/-- The sum of `n` independent `p`-Bernoulli random variables with values in `{1, 0}` follows
the binomial distribution `Bin(n, p)`. -/
theorem hasLaw_sum_of_iIndepFun_bernoulli {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) Ber(1, 0, p) P) (hind : iIndepFun X P) (n : ℕ) :
    HasLaw (fun ω ↦ ∑ k ∈ Finset.range n, X k ω) Bin(ℝ, n, p) P := by
  have hpi := hind.hasLaw_infinitePi hX
    (AEMeasurable.of_eval fun i ↦ (hX i).aemeasurable)
  have hsum : HasLaw (fun x : ℕ → ℝ ↦ ∑ k ∈ Finset.range n, x k) Bin(ℝ, n, p)
      (Measure.infinitePi fun _ : ℕ ↦ Ber((1 : ℝ), 0, p)) :=
    ⟨by fun_prop, infinitePi_bernoulliMeasure_map_sum n⟩
  exact hsum.comp hpi

section DeMoivreLaplace

variable {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Y : Ω' → ℝ}

/-- **de Moivre–Laplace theorem**: for `0 < p < 1`, the standardized binomial distribution
`(Bin(n, p) - n p) / √(n p (1 - p))` converges in distribution to the standard Gaussian. -/
theorem tendstoInDistribution_binomial (hp₀ : p ≠ 0) (hp₁ : p ≠ 1)
    (hY : HasLaw Y (gaussianReal 0 1) P') :
    TendstoInDistribution (fun (n : ℕ) (x : ℝ) ↦ (x - n * p) / √(n * p * (1 - p))) atTop Y
      (fun n ↦ Bin(ℝ, n, p)) P' := by
  set Q := Measure.infinitePi fun _ : ℕ ↦ Ber((1 : ℝ), 0, p)
  set τ := √((p : ℝ) * (1 - p))
  have hp : 0 < (p : ℝ) := lt_of_le_of_ne p.2.1 fun h ↦ hp₀ (Subtype.ext h.symm)
  have hq : 0 < 1 - (p : ℝ) := sub_pos.2 (lt_of_le_of_ne p.2.2 fun h ↦ hp₁ (Subtype.ext h))
  have hs : τ ≠ 0 := (Real.sqrt_pos.2 (mul_pos hp hq)).ne'
  have hs2 : τ ^ 2 = p * (1 - p) := Real.sq_sqrt (mul_pos hp hq).le
  have hX (i : ℕ) : HasLaw (fun x : ℕ → ℝ ↦ x i) Ber((1 : ℝ), 0, p) Q :=
    ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩
  have hind : iIndepFun (fun i (x : ℕ → ℝ) ↦ x i) Q :=
    iIndepFun_infinitePi (X := fun _ (y : ℝ) ↦ y) fun _ ↦ measurable_id
  have hint {f : ℝ → ℝ} (hf : Continuous f) : ∫ x, f (x 0) ∂Q = p * f 1 + (1 - p) * f 0 := by
    rw [← integral_map (measurable_pi_apply 0).aemeasurable hf.aestronglyMeasurable, (hX 0).map_eq,
      integral_bernoulliMeasure, smul_eq_mul, smul_eq_mul]
  let Z : ℕ → (ℕ → ℝ) → ℝ := fun i x ↦ (x i - p) / τ
  have h0 : Q[Z 0] = 0 := by
    rw [hint (f := fun y ↦ (y - p) / τ) (by fun_prop)]
    field_simp
    ring
  have h1 : Q[Z 0 ^ 2] = 1 := by
    rw [show Z 0 ^ 2 = fun x ↦ ((x 0 - p) / τ) ^ 2 from rfl,
      hint (f := fun y ↦ ((y - p) / τ) ^ 2) (by fun_prop)]
    simp only [div_pow, hs2]
    field_simp
    ring
  have hindZ : iIndepFun Z Q := hind.comp (fun _ y ↦ (y - p) / τ) fun _ ↦ by fun_prop
  have hidentZ (i : ℕ) : IdentDistrib (Z i) (Z 0) Q Q :=
    ((hX i).identDistrib (hX 0)).comp (u := fun y ↦ (y - p) / τ) (by fun_prop)
  have hclt := tendstoInDistribution_inv_sqrt_mul_sum hY h0 h1 hindZ hidentZ
  have hlaw (n : ℕ) : Q.map (fun x ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, Z k x) =
      Bin(ℝ, n, p).map fun y : ℝ ↦ (y - n * p) / √(n * p * (1 - p)) := by
    rw [← (hasLaw_sum_of_iIndepFun_bernoulli hX hind n).map_eq,
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    ext x
    simp only [Function.comp_apply, Z]
    rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, show (n : ℝ) * p * (1 - p) = n * (p * (1 - p)) by ring,
      Real.sqrt_mul (Nat.cast_nonneg n), inv_mul_eq_div, div_div, mul_comm τ]
  refine ⟨fun n ↦ by fun_prop, hY.aemeasurable, ?_⟩
  exact hclt.tendsto.congr fun n ↦ Subtype.ext (hlaw n)

/-- **de Moivre–Laplace theorem**, in terms of cumulative distribution functions: for `0 < p < 1`,
the probability that a `Bin(n, p)` random variable `k` satisfies `(k - n p) / √(n p (1 - p)) ≤ x`
tends to `Φ(x)`, where `Φ` is the cumulative distribution function of the standard Gaussian. -/
theorem tendsto_binomial_real_setOf_le (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) (x : ℝ) :
    Tendsto (fun n : ℕ ↦ Bin(n, p).real {k | ((k : ℝ) - n * p) / √(n * p * (1 - p)) ≤ x})
      atTop (𝓝 (cdf (gaussianReal 0 1) x)) := by
  have h := (tendstoInDistribution_binomial hp₀ hp₁ (Y := id) (P' := gaussianReal 0 1)
    ⟨aemeasurable_id, Measure.map_id⟩).tendsto
  have := nullSingletonClass_gaussianReal (μ := 0) one_ne_zero
  have h' := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h (E := Iic x)
    (by simp)
  simp only [ProbabilityMeasure.coe_mk, Measure.map_id] at h'
  rw [cdf_eq_real]
  convert (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h' using 1
  · ext n
    simp only [Function.comp_apply, measureReal_def]
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic,
      Measure.map_apply (by fun_prop) (measurableSet_Iic.preimage (by fun_prop))]
    simp [Set.preimage]
  · simp [measureReal_def]

end DeMoivreLaplace

end ProbabilityTheory
