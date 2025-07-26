/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/

import Mathlib.Probability.Decision.Risk

/-!
# Bayes estimator and generalized Bayes estimator

## Main definitions

* `IsBayesEstimator`: an estimator is a Bayes estimator if it attains the Bayes risk for the prior.
* `IsGenBayesEstimator`: a measurable function `f : 𝓧 → 𝓨` is a generalized Bayes estimator
  with respect to the prior `π` if for `(P ∘ₘ π)`-almost every `x` it has
  the form `x ↦ argmin_z P†π(x)[θ ↦ ℓ θ z]`.
* `HasGenBayesEstimator`: class that states that estimation problem admits a generalized Bayes
  estimator with respect to the prior.

## Main statements

* `IsGenBayesEstimator.isBayesEstimator`: a generalized Bayes estimator is a Bayes estimator.
  That is, it minimizes the Bayesian risk.
* `bayesRiskPrior_eq_of_hasGenBayesEstimator`: if the estimation problem admits a generalized Bayes
estimator, then the Bayesian risk attains the risk lower bound
`∫⁻ x, ⨅ z, ∫⁻ θ, ℓ θ z ∂(P†π) x ∂(P ∘ₘ π)`.

## Implementation details


-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

/-- An estimator is a Bayes estimator for a prior `π` if it attains the Bayes risk for `π`. -/
def IsBayesEstimator (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) : Prop :=
  bayesianRisk ℓ P κ π = bayesRiskPrior ℓ P π

variable [StandardBorelSpace Θ] [Nonempty Θ] {f : 𝓧 → 𝓨} [IsFiniteKernel P] [IsFiniteMeasure π]

/-- We say that a measurable function `f : 𝓧 → 𝓨` is a generalized Bayes estimator
with respect to the prior `π` if for `(P ∘ₘ π)`-almost every `x` it is of
the form `x ↦ argmin_z P†π(x)[θ ↦ ℓ θ z]`. -/
structure IsGenBayesEstimator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (f : 𝓧 → 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] : Prop where
  measurable : Measurable f
  property : ∀ᵐ x ∂(P ∘ₘ π), ∫⁻ θ, ℓ θ (f x) ∂(P†π) x = ⨅ z, ∫⁻ θ, ℓ θ z ∂(P†π) x

/-- Given a generalized Bayes estimator `f`, we can define a deterministic kernel. -/
noncomputable
abbrev IsGenBayesEstimator.kernel (h : IsGenBayesEstimator ℓ P f π) : Kernel 𝓧 𝓨 :=
  Kernel.deterministic f h.measurable

/-- The risk of a generalized Bayes estimator is the risk lower bound
`∫⁻ x, ⨅ z, ∫⁻ θ, ℓ θ z ∂(P†π) x ∂(P ∘ₘ π)`. -/
lemma IsGenBayesEstimator.bayesianRisk_eq_lintegral_iInf (hf : IsGenBayesEstimator ℓ P f π)
    (hl : Measurable (Function.uncurry ℓ)) :
    bayesianRisk ℓ P hf.kernel π = ∫⁻ x, ⨅ z, ∫⁻ θ, ℓ θ z ∂(P†π) x ∂(P ∘ₘ π) := by
  rw [bayesianRisk_eq_lintegral_lintegral_lintegral hl]
  refine lintegral_congr_ae ?_
  filter_upwards [hf.property] with x hx
  rwa [Kernel.deterministic_apply,
    lintegral_dirac' _ (Measurable.lintegral_prod_left (by fun_prop))]

/-- A generalized Bayes estimator is a Bayes estimator: that is, it minimizes the Bayesian risk. -/
lemma IsGenBayesEstimator.isBayesEstimator (hf : IsGenBayesEstimator ℓ P f π)
    (hl : Measurable (Function.uncurry ℓ)) :
    IsBayesEstimator ℓ P hf.kernel π := by
  simp_rw [IsBayesEstimator]
  apply le_antisymm
  · rw [hf.bayesianRisk_eq_lintegral_iInf hl]
    exact lintegral_iInf_posterior_le_bayesRiskPrior hl _ _
  · exact bayesRiskPrior_le_bayesianRisk _ _ _ _

/-- The estimation problem admits a generalized Bayes estimator with respect to the prior `π`. -/
class HasGenBayesEstimator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] where
  /-- The Generalized Bayes estimator. -/
  estimator : 𝓧 → 𝓨
  isGenBayesEstimator : IsGenBayesEstimator ℓ P estimator π

/-- If the estimation problem admits a generalized Bayes estimator, then the Bayesian risk
attains the risk lower bound `∫⁻ x, ⨅ z, ∫⁻ θ, ℓ θ z ∂(P†π) x ∂(P ∘ₘ π)`. -/
lemma bayesRiskPrior_eq_of_hasGenBayesEstimator
    (hl : Measurable (Function.uncurry ℓ)) [h : HasGenBayesEstimator ℓ P π] :
    bayesRiskPrior ℓ P π = ∫⁻ x, ⨅ z, ∫⁻ θ, ℓ θ z ∂((P†π) x) ∂(P ∘ₘ π) := by
  rw [← h.isGenBayesEstimator.isBayesEstimator hl,
    h.isGenBayesEstimator.bayesianRisk_eq_lintegral_iInf hl]

noncomputable instance [Nonempty 𝓨] [Finite 𝓨] : HasGenBayesEstimator ℓ P π where
  estimator x := (Finite.exists_min (fun z ↦ ∫⁻ θ, ℓ θ z ∂(P†π) x)).choose
  isGenBayesEstimator :=
    { measurable := by
        sorry
      property := by
        refine ae_of_all _ fun x ↦ ?_
        have h := (Finite.exists_min (fun z ↦ ∫⁻ θ, ℓ θ z ∂(P†π) x)).choose_spec
        exact le_antisymm (by simpa using h) (iInf_le _ _) }

end ProbabilityTheory
