/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import Mathlib.Probability.Decision.Risk.Basic

/-!
# Risk in countable spaces

## Main statements

* `fooBar_unique`

-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ Θ' 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {mΘ' : MeasurableSpace Θ'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

lemma bayesianRisk_fintype [Fintype Θ] [MeasurableSingletonClass Θ] :
    bayesianRisk ℓ P κ π = ∑ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ} := by
  simp [bayesianRisk, lintegral_fintype]

lemma bayesianRisk_countable [Countable Θ] [MeasurableSingletonClass Θ] :
    bayesianRisk ℓ P κ π = ∑' θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ} := by
  simp [bayesianRisk, lintegral_countable']

lemma bayesianRisk_fintype' [Fintype 𝓨] [MeasurableSingletonClass 𝓨]
    (hl : Measurable (Function.uncurry ℓ)) :
    bayesianRisk ℓ P κ π = ∑ y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π := by
  simp only [bayesianRisk, lintegral_fintype]
  rw [lintegral_finset_sum]
  · congr
  exact fun y _ ↦ Measurable.mul (by fun_prop) ((κ ∘ₖ P).measurable_coe (measurableSet_singleton y))

lemma bayesianRisk_countable' [Countable 𝓨] [MeasurableSingletonClass 𝓨]
    (hl : Measurable (Function.uncurry ℓ)) :
    bayesianRisk ℓ P κ π = ∑' y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π := by
  simp only [bayesianRisk, lintegral_countable']
  rw [lintegral_tsum]
  · rfl
  · refine fun y ↦ Measurable.aemeasurable ?_
    exact Measurable.mul (by fun_prop) ((κ ∘ₖ P).measurable_coe (measurableSet_singleton y))

lemma bayesRiskPrior_fintype [Fintype Θ] [MeasurableSingletonClass Θ] :
    bayesRiskPrior ℓ P π
      = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑ θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ} := by
  simp [bayesRiskPrior, bayesianRisk_fintype]

lemma bayesRiskPrior_countable [Countable Θ] [MeasurableSingletonClass Θ] :
    bayesRiskPrior ℓ P π
      = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑' θ, (∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)) * π {θ} := by
  simp [bayesRiskPrior, bayesianRisk_countable]

lemma bayesRiskPrior_fintype' [Fintype 𝓨] [MeasurableSingletonClass 𝓨]
    (hl : Measurable (Function.uncurry ℓ)) :
    bayesRiskPrior ℓ P π
      = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑ y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π := by
  simp [bayesRiskPrior, bayesianRisk_fintype' hl]

lemma bayesRiskPrior_countable' [Countable 𝓨] [MeasurableSingletonClass 𝓨]
    (hl : Measurable (Function.uncurry ℓ)) :
    bayesRiskPrior ℓ P π
      = ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ∑' y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ P θ) {y} ∂π := by
  simp [bayesRiskPrior, bayesianRisk_countable' hl]

lemma bayesianRisk_const_of_fintype [Fintype 𝓨] [MeasurableSingletonClass 𝓨]
    (hℓ : Measurable (Function.uncurry ℓ)) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    bayesianRisk ℓ (Kernel.const Θ μ) κ π = ∑ y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ μ) {y} ∂π := by
  simp [bayesianRisk_fintype' hℓ]

lemma bayesianRisk_const_of_countable [Countable 𝓨] [MeasurableSingletonClass 𝓨]
    (hℓ : Measurable (Function.uncurry ℓ)) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    bayesianRisk ℓ (Kernel.const Θ μ) κ π = ∑' y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ μ) {y} ∂π := by
  simp [bayesianRisk_countable' hℓ]

lemma bayesRiskPrior_const_of_fintype [Nonempty 𝓨] [Fintype 𝓨] [MeasurableSingletonClass 𝓨]
    (hℓ : Measurable (Function.uncurry ℓ)) (μ : Measure 𝓧) (π : Measure Θ) :
    bayesRiskPrior ℓ (Kernel.const Θ μ) π = ⨅ y, ∫⁻ θ, ℓ θ y * μ .univ ∂π := by
  refine le_antisymm ((bayesRiskPrior_le_inf' hℓ _ _).trans_eq (by simp)) ?_
  simp only [bayesRiskPrior, bayesianRisk_const_of_fintype hℓ, le_iInf_iff]
  intro κ hκ
  calc ⨅ y, ∫⁻ θ, ℓ θ y * μ Set.univ ∂π
  _ = (⨅ y, ∫⁻ θ, ℓ θ y ∂π) * (κ ∘ₘ μ) Set.univ := by
    simp only [Measure.comp_apply_univ]
    rw [ENNReal.iInf_mul' (fun _ h ↦ ?_) (fun _ ↦ inferInstance)]
    · congr with y
      rw [lintegral_mul_const _ (by fun_prop)]
    · rwa [← bot_eq_zero, iInf_eq_bot_iff_of_finite, bot_eq_zero] at h
  _ ≤ ∫⁻ y, ∫⁻ θ, ℓ θ y ∂π ∂(κ ∘ₘ μ) := iInf_mul_le_lintegral (κ ∘ₘ μ) _
  _ = ∑ y, ∫⁻ θ, ℓ θ y * (κ ∘ₘ μ) {y} ∂π := by
    simp only [lintegral_fintype]
    congr with y
    rw [lintegral_mul_const _ (by fun_prop)]

end ProbabilityTheory
