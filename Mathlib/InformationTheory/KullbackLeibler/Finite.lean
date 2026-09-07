/-
Copyright (c) 2026 Elazar Gershuni. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elazar Gershuni
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Kullback-Leibler divergence on finite spaces

This file expresses `klDiv` as a sum over singleton masses on a finite space.
The formulas assume absolute continuity; otherwise `klDiv` is infinite.
For finite measures, the formula includes the correction term `ν.real univ - μ.real univ`.
For probability measures, it is the usual sum `∑ x, μ.real {x} * log (μ.real {x} / ν.real {x})`.

## Main statements

* `klDiv_eq_sum`, `toReal_klDiv_eq_sum`: sum formulas for finite measures.
* `klDiv_eq_sum_of_isProbabilityMeasure`: the sum formula for probability measures.
* `klDiv_sum_smul_dirac`, `toReal_klDiv_sum_smul_dirac`: formulas for weighted Dirac measures.

## References

* [Wikipedia, *Gibbs' inequality*](https://en.wikipedia.org/wiki/Gibbs%27_inequality)
-/

public section

open Real MeasureTheory Set
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α]
  {μ ν : Measure α}

namespace MeasureTheory

lemma integral_llr_fintype [IsFiniteMeasure μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∫ x, llr μ ν x ∂μ = ∑ x, μ.real {x} * log (μ.real {x} / ν.real {x}) := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases hx : ν {x} = 0
  · simp [measureReal_def, hμν hx]
  · rw [smul_eq_mul, llr, Measure.rnDeriv_singleton hμν hx, ENNReal.toReal_div]
    rfl

end MeasureTheory

namespace InformationTheory

lemma klDiv_eq_sum [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    klDiv μ ν = ENNReal.ofReal
      ((∑ x, μ.real {x} * log (μ.real {x} / ν.real {x})) + ν.real univ - μ.real univ) := by
  rw [klDiv_of_ac_of_integrable hμν Integrable.of_finite, integral_llr_fintype hμν]

lemma toReal_klDiv_eq_sum [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal =
      (∑ x, μ.real {x} * log (μ.real {x} / ν.real {x})) + ν.real univ - μ.real univ := by
  rw [toReal_klDiv hμν Integrable.of_finite, integral_llr_fintype hμν]

lemma klDiv_eq_sum_of_isProbabilityMeasure [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) :
    klDiv μ ν = ENNReal.ofReal (∑ x, μ.real {x} * log (μ.real {x} / ν.real {x})) := by
  simp [klDiv_eq_sum hμν]

lemma toReal_klDiv_eq_sum_of_isProbabilityMeasure
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    (klDiv μ ν).toReal = ∑ x, μ.real {x} * log (μ.real {x} / ν.real {x}) := by
  simp [toReal_klDiv_eq_sum hμν]

lemma klDiv_sum_smul_dirac (p q : α → ℝ≥0) (hpq : ∀ x, q x = 0 → p x = 0) :
    klDiv (Measure.sum fun x ↦ p x • Measure.dirac x)
      (Measure.sum fun x ↦ q x • Measure.dirac x) =
      ENNReal.ofReal ((∑ x, p x * log (p x / q x)) + ∑ x, (q x : ℝ) - ∑ x, (p x : ℝ)) := by
  rw [klDiv_eq_sum]
  · simp only [measureReal_def, ← Measure.coe_nnreal_smul, Measure.sum_smul_dirac_singleton]
    simp [ENNReal.toReal_sum]
  · simpa only [← Measure.coe_nnreal_smul, Measure.absolutelyContinuous_sum_smul_dirac_iff,
      ENNReal.coe_eq_zero] using hpq

lemma toReal_klDiv_sum_smul_dirac (p q : α → ℝ≥0) (hpq : ∀ x, q x = 0 → p x = 0) :
    (klDiv (Measure.sum fun x ↦ p x • Measure.dirac x)
      (Measure.sum fun x ↦ q x • Measure.dirac x)).toReal =
      (∑ x, p x * log (p x / q x)) + ∑ x, (q x : ℝ) - ∑ x, (p x : ℝ) := by
  rw [toReal_klDiv_eq_sum]
  · simp only [measureReal_def, ← Measure.coe_nnreal_smul, Measure.sum_smul_dirac_singleton]
    simp [ENNReal.toReal_sum]
  · simpa only [← Measure.coe_nnreal_smul, Measure.absolutelyContinuous_sum_smul_dirac_iff,
      ENNReal.coe_eq_zero] using hpq

end InformationTheory
