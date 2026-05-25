/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

--public import Mathlib.Probability.Decision.AuxLemmas
public import Mathlib.Probability.Decision.Risk.Defs
public import Mathlib.Probability.Kernel.Posterior

import Mathlib.Probability.Decision.Risk.Basic

/-!
# Bayes estimator

Let `Θ` be a parameter space, `𝓧` a data space, `𝓨` a prediction space, `P : Kernel Θ 𝓧` a
data generating kernel, `π` a prior on the parameter space, and `ℓ : Θ → 𝓨 → ℝ≥0∞` a loss function.

An estimator (a `Kernel 𝓧 𝓨`) is said to be a Bayes estimator if it attains the Bayes risk for
the estimation problem.
It can be written as a measurable function `x ↦ argmin_y P†π(x)[θ ↦ ℓ θ y]`
for `(P ∘ₘ π)`-almost every `x`, where `P†π` is the posterior kernel, whenever we can select
the argmin in a measurable way.

## Main definitions

* `IsBayesEstimator`: an estimator is a Bayes estimator if it attains the Bayes risk for the prior.
* `IsArgminEstimator`: a measurable function `f : 𝓧 → 𝓨` is an argmin estimator
  with respect to the prior `π` if for `(P ∘ₘ π)`-almost every `x` it has
  the form `x ↦ argmin_y P†π(x)[θ ↦ ℓ θ y]`.
* `HasArgminEstimator`: class that states that estimation problem admits an argmin Bayes
  estimator with respect to the prior. That is, we can choose the argmin of the posterior expected
  loss in a measurable way.

## Main statements

* `lintegral_iInf_posterior_le_bayesRisk`: the Bayes risk with respect to a prior is bounded
  from below by the integral over the data (with distribution `P ∘ₘ π`) of the infimum over the
  possible predictions `y` of the posterior loss `∫⁻ θ, ℓ θ y ∂((P†π) x)`:
  `∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) ≤ bayesRisk ℓ P π`
* `IsArgminEstimator.isBayesEstimator`: an argmin Bayes estimator is a Bayes estimator.
  That is, it minimizes the Bayesian risk.
* `bayesRisk_eq_of_hasArgminEstimator`: if the estimation problem admits an argmin estimator,
  then the Bayesian risk attains the risk lower bound `∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂(P ∘ₘ π)`.

-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

section Posterior

variable [StandardBorelSpace Θ] [Nonempty Θ]

/-- The Bayesian risk of an estimator `κ` with respect to a prior `π` can be expressed as
an integral in the following way: `R_π(κ) = ((P†π × κ) ∘ P ∘ π)[(θ, z) ↦ ℓ(y(θ), z)]`. -/
lemma avgRisk_eq_lintegral_posterior_prod
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] [IsSFiniteKernel κ] :
    avgRisk ℓ P κ π = ∫⁻ θy, ℓ θy.1 θy.2 ∂(((P†π) ×ₖ κ) ∘ₘ (P ∘ₘ π)) := by
  simp only [avgRisk]
  rw [← Measure.lintegral_compProd (f := fun θy ↦ ℓ θy.1 θy.2) (by fun_prop)]
  congr
  calc π ⊗ₘ (κ ∘ₖ P) = (Kernel.id ∥ₖ κ) ∘ₘ (π ⊗ₘ P) := Measure.parallelComp_comp_compProd.symm
  _ = (Kernel.id ∥ₖ κ) ∘ₘ ((P†π) ×ₖ Kernel.id) ∘ₘ P ∘ₘ π := by rw [posterior_prod_id_comp]
  _ = ((P†π) ×ₖ κ) ∘ₘ P ∘ₘ π := by
      rw [Measure.comp_assoc, Kernel.parallelComp_comp_prod, Kernel.id_comp, Kernel.comp_id]

lemma avgRisk_eq_lintegral_lintegral_lintegral
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] [IsSFiniteKernel κ] :
    avgRisk ℓ P κ π = ∫⁻ x, ∫⁻ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂κ x ∂(P ∘ₘ π) := by
  rw [avgRisk_eq_lintegral_posterior_prod hl,
    Measure.lintegral_bind ((P†π) ×ₖ κ).aemeasurable (by fun_prop)]
  congr with x
  rw [Kernel.prod_apply, lintegral_prod_symm' _ (by fun_prop)]

lemma lintegral_iInf_posterior_le_avgRisk
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] [IsMarkovKernel κ] :
    ∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) ≤ avgRisk ℓ P κ π := by
  rw [avgRisk_eq_lintegral_lintegral_lintegral hl]
  gcongr with x
  exact iInf_le_lintegral _

lemma lintegral_iInf_posterior_le_bayesRisk
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π] :
    ∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) ≤ bayesRisk ℓ P π :=
  le_iInf₂ fun κ _ ↦ lintegral_iInf_posterior_le_avgRisk hl P κ π

end Posterior

/-- An estimator is a Bayes estimator for a prior `π` if it attains the Bayes risk for `π`. -/
def IsBayesEstimator (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) : Prop :=
  avgRisk ℓ P κ π = bayesRisk ℓ P π

variable [StandardBorelSpace Θ] [Nonempty Θ] {f : 𝓧 → 𝓨} [IsFiniteKernel P] [IsFiniteMeasure π]

/-- We say that a measurable function `f : 𝓧 → 𝓨` is an argmin estimator
with respect to the prior `π` if for `(P ∘ₘ π)`-almost every `x` it is of
the form `x ↦ argmin_y P†π(x)[θ ↦ ℓ θ y]`. -/
structure IsArgminEstimator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (f : 𝓧 → 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] : Prop where
  measurable : Measurable f
  property : ∀ᵐ x ∂(P ∘ₘ π), ∫⁻ θ, ℓ θ (f x) ∂(P†π) x = ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x

/-- Given an argmin estimator `f`, we can define a deterministic kernel. -/
noncomputable
abbrev IsArgminEstimator.kernel (h : IsArgminEstimator ℓ P f π) : Kernel 𝓧 𝓨 :=
  Kernel.deterministic f h.measurable

/-- The risk of an argmin estimator is the risk lower bound
`∫⁻ x, ⨅ z, ∫⁻ θ, ℓ θ z ∂(P†π) x ∂(P ∘ₘ π)`. -/
lemma IsArgminEstimator.avgRisk_eq_lintegral_iInf (hf : IsArgminEstimator ℓ P f π)
    (hl : Measurable (Function.uncurry ℓ)) :
    avgRisk ℓ P hf.kernel π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂(P ∘ₘ π) := by
  rw [avgRisk_eq_lintegral_lintegral_lintegral hl]
  refine lintegral_congr_ae ?_
  filter_upwards [hf.property] with x hx
  rwa [Kernel.deterministic_apply,
    lintegral_dirac' _ (Measurable.lintegral_prod_left (by fun_prop))]

/-- An argmin estimator is a Bayes estimator: that is, it minimizes the Bayesian risk. -/
lemma IsArgminEstimator.isBayesEstimator (hf : IsArgminEstimator ℓ P f π)
    (hl : Measurable (Function.uncurry ℓ)) :
    IsBayesEstimator ℓ P hf.kernel π := by
  simp_rw [IsBayesEstimator]
  apply le_antisymm
  · rw [hf.avgRisk_eq_lintegral_iInf hl]
    exact lintegral_iInf_posterior_le_bayesRisk hl _ _
  · exact bayesRisk_le_avgRisk _ _ _ _

-- TODO: delete this and replace it in theorems with hypotheses on `𝓧` and `𝓨`
-- once we have measurable selection theorems?
/-- The estimation problem admits an argmin estimator with respect to the prior `π`.

That is, we can choose the argmin of the posterior expected loss in a measurable way. -/
class HasArgminEstimator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    Prop where
  exists_isArgminEstimator : ∃ f : 𝓧 → 𝓨, IsArgminEstimator ℓ P f π

/-- An estimator for an estimation problem that for `(P ∘ₘ π)`-almost every `x` is of
the form `x ↦ argmin_y P†π(x)[θ ↦ ℓ θ y]`. -/
noncomputable
def argminEstimator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π]
    [h : HasArgminEstimator ℓ P π] : 𝓧 → 𝓨 :=
  h.exists_isArgminEstimator.choose

lemma isArgminEstimator_argminEstimator [h : HasArgminEstimator ℓ P π] :
    IsArgminEstimator ℓ P (argminEstimator ℓ P π) π :=
  h.exists_isArgminEstimator.choose_spec

/-- If the estimation problem admits a generalized Bayes estimator, then the Bayesian risk
attains the risk lower bound `∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π)`. -/
lemma bayesRisk_eq_of_hasArgminEstimator
    (hl : Measurable (Function.uncurry ℓ)) [HasArgminEstimator ℓ P π] :
    bayesRisk ℓ P π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) := by
  rw [← isArgminEstimator_argminEstimator.isBayesEstimator hl,
    isArgminEstimator_argminEstimator.avgRisk_eq_lintegral_iInf hl]

-- /-- If the set of labels `𝓨` is finite, the estimation problem admits a
-- generalized Bayes estimator. -/
-- lemma hasArgminEstimator_of_finite [Nonempty 𝓨] [Finite 𝓨] [MeasurableSingletonClass 𝓨]
--     (hl : Measurable (Function.uncurry ℓ)) :
--     HasArgminEstimator ℓ P π where
--   exists_isArgminEstimator := by
--     classical
--     have : Encodable 𝓨 := Encodable.ofCountable 𝓨
--     have h_meas y : Measurable (fun x ↦ ∫⁻ θ, ℓ θ y ∂(P†π) x) :=
--       (Measure.measurable_lintegral (by fun_prop)).comp (by fun_prop)
--     refine ⟨measurableArgmin (fun x y ↦ ∫⁻ θ, ℓ θ y ∂(P†π) x),
--       measurable_measurableArgmin h_meas, ae_of_all _ fun x ↦ ?_⟩
--     have h := isMinOn_measurableArgmin (fun x y ↦ ∫⁻ θ, ℓ θ y ∂(P†π) x) x
--     exact le_antisymm (by simpa using h) (iInf_le _ _)

end ProbabilityTheory
