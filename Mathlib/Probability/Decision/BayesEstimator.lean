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
  the form `x ↦ argmin_y P†π(x)[θ ↦ ℓ θ y]`.
* `HasGenBayesEstimator`: class that states that estimation problem admits a generalized Bayes
  estimator with respect to the prior.

## Main statements

* `IsGenBayesEstimator.isBayesEstimator`: a generalized Bayes estimator is a Bayes estimator.
  That is, it minimizes the Bayesian risk.
* `bayesRiskPrior_eq_of_hasGenBayesEstimator`: if the estimation problem admits a generalized Bayes
estimator, then the Bayesian risk attains the risk lower bound
`∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂(P ∘ₘ π)`.

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
the form `x ↦ argmin_y P†π(x)[θ ↦ ℓ θ y]`. -/
structure IsGenBayesEstimator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (f : 𝓧 → 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] : Prop where
  measurable : Measurable f
  property : ∀ᵐ x ∂(P ∘ₘ π), ∫⁻ θ, ℓ θ (f x) ∂(P†π) x = ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x

/-- Given a generalized Bayes estimator `f`, we can define a deterministic kernel. -/
noncomputable
abbrev IsGenBayesEstimator.kernel (h : IsGenBayesEstimator ℓ P f π) : Kernel 𝓧 𝓨 :=
  Kernel.deterministic f h.measurable

/-- The risk of a generalized Bayes estimator is the risk lower bound
`∫⁻ x, ⨅ z, ∫⁻ θ, ℓ θ z ∂(P†π) x ∂(P ∘ₘ π)`. -/
lemma IsGenBayesEstimator.bayesianRisk_eq_lintegral_iInf (hf : IsGenBayesEstimator ℓ P f π)
    (hl : Measurable (Function.uncurry ℓ)) :
    bayesianRisk ℓ P hf.kernel π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂(P ∘ₘ π) := by
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
attains the risk lower bound `∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π)`. -/
lemma bayesRiskPrior_eq_of_hasGenBayesEstimator
    (hl : Measurable (Function.uncurry ℓ)) [h : HasGenBayesEstimator ℓ P π] :
    bayesRiskPrior ℓ P π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) := by
  rw [← h.isGenBayesEstimator.isBayesEstimator hl,
    h.isGenBayesEstimator.bayesianRisk_eq_lintegral_iInf hl]

lemma measurableSet_isMin {α : Type*} {_ : MeasurableSpace α} [TopologicalSpace α] [PartialOrder α]
    [OpensMeasurableSpace α] [OrderClosedTopology α] [SecondCountableTopology α]
    [Countable 𝓨]
    {f : 𝓧 → 𝓨 → α} (hf : ∀ y, Measurable (fun x ↦ f x y)) (y : 𝓨) :
    MeasurableSet {x | IsMinOn (f x) .univ y} := by
  simp only [isMinOn_univ_iff]
  rw [show {x | ∀ y', f x y ≤ f x y'} = ⋂ y', {x | f x y ≤ f x y'} by ext; simp]
  exact MeasurableSet.iInter fun z ↦ measurableSet_le (by fun_prop) (by fun_prop)

lemma exists_isMinOn {α : Type*} {_ : MeasurableSpace α} [TopologicalSpace α] [LinearOrder α]
    [OpensMeasurableSpace α] [OrderClosedTopology α] [SecondCountableTopology α]
    [Nonempty 𝓨] [Finite 𝓨] (f : 𝓧 → 𝓨 → α) (x : 𝓧) :
    ∃ y, IsMinOn (f x) .univ y := by
  simpa only [isMinOn_univ_iff] using Finite.exists_min (f x)

lemma exists_isMinOn' {α : Type*} {_ : MeasurableSpace α} [TopologicalSpace α] [LinearOrder α]
    [OpensMeasurableSpace α] [OrderClosedTopology α] [SecondCountableTopology α]
    [Nonempty 𝓨] [Finite 𝓨] (f : 𝓧 → 𝓨 → α) (x : 𝓧) :
    ∃ n : ℕ, ∃ y, n = (Encodable.ofCountable 𝓨).encode y ∧ IsMinOn (f x) .univ y := by
  obtain ⟨y, h⟩ := exists_isMinOn f x
  exact ⟨(Encodable.ofCountable 𝓨).encode y, y, rfl, h⟩

open Classical in
noncomputable
def measurableArgmin {α : Type*} {_ : MeasurableSpace α} [TopologicalSpace α] [LinearOrder α]
    [OpensMeasurableSpace α] [OrderClosedTopology α] [SecondCountableTopology α]
    [Nonempty 𝓨] [Finite 𝓨]
    (f : 𝓧 → 𝓨 → α) (x : 𝓧) :
    𝓨 :=
  sorry

lemma measurable_measurableArgmin {α : Type*} {_ : MeasurableSpace α}
    [TopologicalSpace α] [LinearOrder α]
    [OpensMeasurableSpace α] [OrderClosedTopology α] [SecondCountableTopology α]
    [Nonempty 𝓨] [Finite 𝓨]
    {f : 𝓧 → 𝓨 → α} (hf : ∀ y, Measurable (fun x ↦ f x y))
    (h_exists : ∀ x, ∃ y, IsMinOn (f x) .univ y) :
    Measurable (measurableArgmin f) := by
  unfold measurableArgmin
  sorry

lemma isMinOn_measurableArgmin {α : Type*} {_ : MeasurableSpace α}
    [TopologicalSpace α] [LinearOrder α]
    [OpensMeasurableSpace α] [OrderClosedTopology α] [SecondCountableTopology α]
    [Nonempty 𝓨] [Finite 𝓨]
    {f : 𝓧 → 𝓨 → α} (hf : ∀ y, Measurable (fun x ↦ f x y))
    (h_exists : ∀ x, ∃ y, IsMinOn (f x) .univ y) (x : 𝓧) :
    IsMinOn (f x) .univ (measurableArgmin f x) := by
  sorry

lemma todo [Nonempty 𝓨] [Finite 𝓨] (hl : Measurable (Function.uncurry ℓ)) (y : 𝓨) :
    Measurable (fun x ↦ ∫⁻ θ, ℓ θ y ∂(P†π) x) :=
  (Measure.measurable_lintegral (by fun_prop)).comp (by fun_prop)

lemma todo' [Nonempty 𝓨] [Finite 𝓨] (x : 𝓧) :
    ∃ y, IsMinOn ((fun x y ↦ ∫⁻ (θ : Θ), ℓ θ y ∂(P†π) x) x) Set.univ y := by
  simp only [isMinOn_univ_iff]
  exact Finite.exists_min _

noncomputable instance [Nonempty 𝓨] [Finite 𝓨] (hl : Measurable (Function.uncurry ℓ)) :
    HasGenBayesEstimator ℓ P π where
  estimator x := measurableArgmin (fun x y ↦ ∫⁻ θ, ℓ θ y ∂(P†π) x) x
  isGenBayesEstimator :=
    { measurable := measurable_measurableArgmin (todo hl) todo'
      property := by
        refine ae_of_all _ fun x ↦ ?_
        have h := isMinOn_measurableArgmin (f := fun x y ↦ ∫⁻ θ, ℓ θ y ∂(P†π) x) (todo hl)
         todo' x
        exact le_antisymm (by simpa [isMinOn_univ_iff] using h) (iInf_le _ _) }

end ProbabilityTheory
