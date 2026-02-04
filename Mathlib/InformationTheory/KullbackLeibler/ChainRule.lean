/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Notation

import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# Chain rule for the Kullback-Leibler divergence

Suppose that we have two finite joint measures on a product `α × β`, which can be decomposed as
`μ ⊗ₘ κ` and `ν ⊗ₘ η`, where `μ` and `ν` are measures on `α` and `κ` and `η` are Markov kernels
from `α` to `β`. Then we can express the Kullback-Leibler divergence between these two joint
measures as a sum of `klDiv μ ν` and the conditional Kullback-Leibler divergence between the kernels
`κ` and `η`, averaged over `μ`. The resulting equality is most often written as
`klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + μ[fun x ↦ klDiv (κ x) (η x)]`.

Here we first prove the following version:
`klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`.
This version avoids the issue of measurability of the function `x ↦ klDiv (κ x) (η x)`, which is not
always guaranteed, and thus holds for all measurable spaces `α` and `β`, without any assumptions.

## Main statements

* `klDiv_compProd_eq_add`: `klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`

## Proof

The Kullback-Leibler divergence `klDiv μ ν` is defined with an if-then-else statement:
if the measures are absolutely continuous (`μ ≪ ν`) and the log-likelihood ratio `llr μ ν` is
integrable, then it is defined as `∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ`, otherwise
it is defined to be `∞`.

We first deal with the case in which absolute continuity does not hold. The crucial observation is
that `μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ μ ⊗ₘ κ ≪ μ ⊗ₘ η`, which means that if one of the two sides of the
KL equality is infinite because of lack of absolute continuity, then the other side is also infinite
for the same reason.

Then, we deal with the case in which absolute continuity holds but integrability does not. Again,
we can show a similar equivalence for integrability, which allows us to conclude that both sides
are infinite.
`Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)` is equivalent to
`Integrable (llr μ ν) μ ∧ Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ)`.
This is harder to prove than the absolute continuity and relies on the convexity of
the function `x ↦ x * log x`.

Finally, we prove the equality in the case in which both absolute continuity and integrability hold.
In that case, `klDiv μ ν = ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ` and similarly for
the other terms. It is easy to see that it suffices to prove the equality of the integrals parts.
The main ingredient is the chain rule for Radon-Nikodym derivatives:
`∂(μ ⊗ₘ κ)/∂(ν ⊗ₘ η) = ∂μ/∂ν * ∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)`.
Finally, the computation for the integral of the log-likelihood ratio is as follows:
```
∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂(μ ⊗ₘ κ)
_ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * log ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal ∂(ν ⊗ₘ η)
_ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal *
    (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(ν ⊗ₘ η)
_ = ∫ p, (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(μ ⊗ₘ κ)
_ = ∫ p, log ((∂μ/∂ν) p.1).toReal ∂(μ ⊗ₘ κ) + ∫ p, log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal ∂(μ ⊗ₘ κ)
_ = ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ)
```

## TODO

Add a version of the chain rule for the integral form of the contional KL divergence, i.e.
`μ[fun x ↦ klDiv (κ x) (η x)]`.

-/

@[expose] public section

open Real MeasureTheory Set ProbabilityTheory

open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β}

/-- If the log-likelihood ration between two composition-products is integrable, then so is the
log-likelihood ratio between the two measures on the first space.
See `integrable_llr_compProd_iff` for a stronger result. -/
lemma integrable_llr_of_integrable_llr_compProd
    [IsMarkovKernel κ] [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    Integrable (llr μ ν) μ := by
  have ⟨hμν_ac, hκη_ac⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  rw [← integrable_rnDeriv_mul_log_iff h_ac] at h_int
  replace h_int := convexOn_mul_log.integrable_apply_rnDeriv_of_integrable_compProd
    continuous_mul_log.stronglyMeasurable continuous_mul_log.continuousOn h_int hκη_ac
  exact (integrable_rnDeriv_mul_log_iff hμν_ac).mp h_int

lemma rnDeriv_compProd_mul_log_eq_mul_add [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    ∀ᵐ p ∂(ν ⊗ₘ η), ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * log ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal =
      (((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * (log ((∂μ/∂ν) p.1).toReal +
        log ((∂(μ ⊗ₘ κ)/∂(μ ⊗ₘ η)) p).toReal)) := by
  filter_upwards [rnDeriv_compProd h_ac ν] with p hp
  simp_rw [hp]
  simp only [ENNReal.toReal_mul]
  by_cases h_zero1 : ((∂μ/∂ν) p.1).toReal = 0
  · simp [h_zero1]
  by_cases h_zero2 : ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal = 0
  · simp [h_zero2]
  simp [log_mul h_zero1 h_zero2]

lemma integrable_llr_compProd_iff [IsMarkovKernel κ]
    [IsMarkovKernel η] [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ↔
      Integrable (llr μ ν) μ ∧ Integrable (llr (μ ⊗ₘ κ) (μ ⊗ₘ η)) (μ ⊗ₘ κ) := by
  have ⟨h_ac_μν, h_ac_κη⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  rw [← integrable_rnDeriv_mul_log_iff h_ac,
    integrable_congr (rnDeriv_compProd_mul_log_eq_mul_add h_ac_κη)]
  have : Integrable (fun x ↦ ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) x).toReal *
        (log ((∂μ/∂ν) x.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x).toReal)) (ν ⊗ₘ η) ↔
      Integrable (fun x ↦ (log ((∂μ/∂ν) x.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x).toReal))
        (μ ⊗ₘ κ) := integrable_rnDeriv_smul_iff h_ac
  rw [this]
  have h_iff_κ : Integrable (llr μ ν) μ ↔ Integrable (fun x ↦ llr μ ν x.1) (μ ⊗ₘ κ) := by
    rw [Measure.integrable_compProd_iff]
    swap; · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
    simp only [ne_eq, enorm_ne_top, not_false_eq_true, integrable_const_enorm,
      Filter.eventually_true, norm_eq_abs, integral_const, probReal_univ, smul_eq_mul, one_mul,
      true_and]
    rw [← integrable_norm_iff (by fun_prop)]
    simp
  rw [h_iff_κ]
  -- Goal of the form `Integrable (f + g) ↔ Integrable f ∧ Integrable g`
  refine ⟨fun h_int ↦ ?_, fun ⟨h_int1, h_int2⟩ ↦ h_int1.add h_int2⟩
  -- We now prove `Integrable (f + g) → Integrable f ∧ Integrable g`.
  -- We have one of those implications from the lemma `integrable_llr_of_integrable_llr_compProd`,
  -- say `Integrable (f + g) → Integrable f`.
  -- But given `Integrable f`, we have `Integrable (f + g) ↔ Integrable g` and thus we can also
  -- conclude `Integrable g`.
  have h_int_iff : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ) ↔
      Integrable (fun x ↦ log ((∂μ/∂ν) x.1).toReal +
        log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) x).toReal) (μ ⊗ₘ κ) := by
    have ⟨h_ac_μν, h_ac_κη⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
    rw [← integrable_rnDeriv_mul_log_iff h_ac,
     integrable_congr (rnDeriv_compProd_mul_log_eq_mul_add h_ac_κη)]
    exact integrable_rnDeriv_smul_iff h_ac
  rw [← h_int_iff] at h_int
  have h_int1 := integrable_llr_of_integrable_llr_compProd h_ac h_int
  rw [h_iff_κ] at h_int1
  rw [h_int_iff, integrable_add_iff_integrable_right'] at h_int
  · refine ⟨h_int1, h_int⟩
  · exact h_int1

/-- Chain rule for the integral of the log-likelihood ratio, under absolute continuity and
integrability assumptions. -/
lemma integral_llr_compProd_eq_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ]
    [IsMarkovKernel η] (h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η)
    (h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)) :
    ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂μ ⊗ₘ κ =
      ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) := by
  have ⟨h_ac_μν, h_ac_κη⟩ := Measure.absolutelyContinuous_compProd_iff.mp h_ac
  have ⟨h_int_μν, h_int_κη⟩ := (integrable_llr_compProd_iff h_ac).mp h_int
  have h_int1 : Integrable (fun p ↦ log ((∂μ/∂ν) p.1).toReal) (μ ⊗ₘ κ) := by
    rw [Measure.integrable_compProd_iff]
    · simp only [ne_eq, enorm_ne_top, not_false_eq_true, integrable_const_enorm,
        Filter.eventually_true, norm_eq_abs, integral_const, probReal_univ, smul_eq_mul, one_mul,
        true_and]
      rw [← integrable_norm_iff (by fun_prop)] at h_int_μν
      convert h_int_μν
    · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  calc ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂μ ⊗ₘ κ
  _ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal * log ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal ∂(ν ⊗ₘ η) := by
    rw [integral_rnDeriv_mul_log h_ac]
  _ = ∫ p, ((∂μ ⊗ₘ κ/∂ν ⊗ₘ η) p).toReal *
      (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(ν ⊗ₘ η) :=
    integral_congr_ae (rnDeriv_compProd_mul_log_eq_mul_add h_ac_κη)
  _ = ∫ p, (log ((∂μ/∂ν) p.1).toReal + log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal) ∂(μ ⊗ₘ κ) :=
    integral_rnDeriv_smul h_ac
  _ = ∫ p, log ((∂μ/∂ν) p.1).toReal ∂(μ ⊗ₘ κ) +
      ∫ p, log ((∂μ ⊗ₘ κ/∂μ ⊗ₘ η) p).toReal ∂(μ ⊗ₘ κ) := by
    rw [integral_add h_int1]
    exact h_int_κη.ofReal
  _ = ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) := by
    congr
    rw [Measure.integral_compProd h_int1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rfl

variable (μ ν κ η) in
/-- **Chain rule** for the Kullback-Leibler divergence, with conditional KL expressed using
composition-products.
This version holds without any assumption on the measurable spaces. -/
theorem klDiv_compProd_eq_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ]
    [IsMarkovKernel η] :
    klDiv (μ ⊗ₘ κ) (ν ⊗ₘ η) = klDiv μ ν + klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) := by
  have h_ac_iff : μ ⊗ₘ κ ≪ ν ⊗ₘ η ↔ μ ≪ ν ∧ μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.absolutelyContinuous_compProd_iff
  -- first, if we don't have absolute continuity, both sides are `∞`
  by_cases h_ac : μ ⊗ₘ κ ≪ ν ⊗ₘ η
  swap
  · rw [klDiv_of_not_ac h_ac]
    rw [h_ac_iff] at h_ac
    simp only [not_and_or] at h_ac
    cases h_ac with
    | inl h => simp [h]
    | inr h => simp [h]
  -- same if we don't have integrability
  by_cases h_int : Integrable (llr (μ ⊗ₘ κ) (ν ⊗ₘ η)) (μ ⊗ₘ κ)
  swap
  · rw [klDiv_of_not_integrable h_int]
    rw [integrable_llr_compProd_iff h_ac] at h_int
    simp only [not_and_or] at h_int
    cases h_int with
    | inl h => simp [h]
    | inr h => simp [h]
  -- now we can use express the KL divergences with an integral of a log-likelihood ratio
  have ⟨h_ac_μν, h_ac_κη⟩ := h_ac_iff.mp h_ac
  have ⟨h_int_μν, h_int_κη⟩ := (integrable_llr_compProd_iff h_ac).mp h_int
  rw [klDiv_of_ac_of_integrable h_ac h_int, klDiv_of_ac_of_integrable h_ac_μν h_int_μν,
    klDiv_of_ac_of_integrable h_ac_κη h_int_κη]
  rw [← ENNReal.ofReal_add (integral_llr_add_sub_measure_univ_nonneg h_ac_μν h_int_μν)
    (integral_llr_add_sub_measure_univ_nonneg h_ac_κη h_int_κη)]
  simp_rw [measureReal_def, Measure.compProd_apply_univ]
  rw [add_sub_cancel_right]
  -- it suffices to prove the chain rule for the integrals of log-likelihood ratios
  suffices ∫ p, llr (μ ⊗ₘ κ) (ν ⊗ₘ η) p ∂μ ⊗ₘ κ =
      ∫ a, llr μ ν a ∂μ + ∫ p, llr (μ ⊗ₘ κ) (μ ⊗ₘ η) p ∂(μ ⊗ₘ κ) by rw [this]; ring_nf
  -- the result follows from a previous lemma
  exact integral_llr_compProd_eq_add h_ac h_int

end InformationTheory
