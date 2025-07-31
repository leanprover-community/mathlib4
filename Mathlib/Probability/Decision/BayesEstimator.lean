/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/

import Mathlib.Probability.Decision.Risk.Basic
import Mathlib.Probability.Kernel.Posterior

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

section Posterior

variable [StandardBorelSpace Θ] [Nonempty Θ]

/-- The Bayesian risk of an estimator `κ` with respect to a prior `π` can be expressed as
an integral in the following way: `R_π(κ) = ((P†π × κ) ∘ P ∘ π)[(θ, z) ↦ ℓ(y(θ), z)]`. -/
lemma bayesianRisk_eq_lintegral_posterior_prod
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] [IsSFiniteKernel κ] :
    bayesianRisk ℓ P κ π = ∫⁻ θy, ℓ θy.1 θy.2 ∂(((P†π) ×ₖ κ) ∘ₘ (P ∘ₘ π)) := by
  simp only [bayesianRisk]
  rw [← Measure.lintegral_compProd (f := fun θy ↦ ℓ θy.1 θy.2) (by fun_prop)]
  congr
  calc π ⊗ₘ (κ ∘ₖ P) = (Kernel.id ∥ₖ κ) ∘ₘ (π ⊗ₘ P) := Measure.parallelComp_comp_compProd.symm
  _ = (Kernel.id ∥ₖ κ) ∘ₘ ((P†π) ×ₖ Kernel.id) ∘ₘ P ∘ₘ π := by rw [posterior_prod_id_comp]
  _ = ((P†π) ×ₖ κ) ∘ₘ P ∘ₘ π := by
      rw [Measure.comp_assoc, Kernel.parallelComp_comp_prod, Kernel.id_comp, Kernel.comp_id]

lemma bayesianRisk_eq_lintegral_lintegral_lintegral
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] [IsSFiniteKernel κ] :
    bayesianRisk ℓ P κ π = ∫⁻ x, ∫⁻ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂κ x ∂(P ∘ₘ π) := by
  rw [bayesianRisk_eq_lintegral_posterior_prod hl,
    Measure.lintegral_bind ((P†π) ×ₖ κ).aemeasurable (by fun_prop)]
  congr with x
  rw [Kernel.prod_apply, lintegral_prod_symm' _ (by fun_prop)]

lemma lintegral_iInf_posterior_le_bayesianRisk
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] [IsMarkovKernel κ] :
    ∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) ≤ bayesianRisk ℓ P κ π := by
  rw [bayesianRisk_eq_lintegral_lintegral_lintegral hl]
  gcongr with x
  exact iInf_le_lintegral _ _

lemma lintegral_iInf_posterior_le_bayesRiskPrior
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π] :
    ∫⁻ x, ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) ≤ bayesRiskPrior ℓ P π :=
  le_iInf₂ fun κ _ ↦ lintegral_iInf_posterior_le_bayesianRisk hl P κ π

end Posterior

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
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    Prop where
  exists_isGenBayesEstimator : ∃ f : 𝓧 → 𝓨, IsGenBayesEstimator ℓ P f π

noncomputable
def HasGenBayesEstimator.estimator (h : HasGenBayesEstimator ℓ P π) : 𝓧 → 𝓨 :=
  h.exists_isGenBayesEstimator.choose

lemma HasGenBayesEstimator.isGenBayesEstimator (h : HasGenBayesEstimator ℓ P π) :
    IsGenBayesEstimator ℓ P h.estimator π :=
  h.exists_isGenBayesEstimator.choose_spec

/-- If the estimation problem admits a generalized Bayes estimator, then the Bayesian risk
attains the risk lower bound `∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π)`. -/
lemma bayesRiskPrior_eq_of_hasGenBayesEstimator
    (hl : Measurable (Function.uncurry ℓ)) [h : HasGenBayesEstimator ℓ P π] :
    bayesRiskPrior ℓ P π = ∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂((P†π) x) ∂(P ∘ₘ π) := by
  rw [← h.isGenBayesEstimator.isBayesEstimator hl,
    h.isGenBayesEstimator.bayesianRisk_eq_lintegral_iInf hl]

section Finite

variable {α : Type*} {_ : MeasurableSpace α} [TopologicalSpace α] [LinearOrder α]
    [OpensMeasurableSpace α] [OrderClosedTopology α] [SecondCountableTopology α]

lemma measurableSet_isMin [Countable 𝓨]
    {f : 𝓧 → 𝓨 → α} (hf : ∀ y, Measurable (fun x ↦ f x y)) (y : 𝓨) :
    MeasurableSet {x | ∀ z, f x y ≤ f x z} := by
  rw [show {x | ∀ y', f x y ≤ f x y'} = ⋂ y', {x | f x y ≤ f x y'} by ext; simp]
  exact MeasurableSet.iInter fun z ↦ measurableSet_le (by fun_prop) (by fun_prop)

lemma exists_isMinOn' {α : Type*} [LinearOrder α]
    [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] (f : 𝓧 → 𝓨 → α) (x : 𝓧) :
    ∃ n : ℕ, ∃ y, n = Encodable.encode y ∧ ∀ z, f x y ≤ f x z := by
  obtain ⟨y, h⟩ := Finite.exists_min (f x)
  exact ⟨Encodable.encode y, y, rfl, h⟩

noncomputable
def measurableArgmin [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] [MeasurableSingletonClass 𝓨]
    [(x : ℕ) → Decidable (x ∈ Set.range (Encodable.encode (α := 𝓨)))]
    (f : 𝓧 → 𝓨 → α)
    [∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x y ≤ f x z]
    (x : 𝓧) :
    𝓨 :=
  (measurableEmbedding_encode 𝓨).invFun (Nat.find (exists_isMinOn' f x))

lemma measurable_measurableArgmin [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] [MeasurableSingletonClass 𝓨]
    [(x : ℕ) → Decidable (x ∈ Set.range (Encodable.encode (α := 𝓨)))]
    {f : 𝓧 → 𝓨 → α}
    [∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x y ≤ f x z]
    (hf : ∀ y, Measurable (fun x ↦ f x y)) :
    Measurable (measurableArgmin f) := by
  refine (MeasurableEmbedding.measurable_invFun (measurableEmbedding_encode 𝓨)).comp ?_
  refine measurable_find _ fun n ↦ ?_
  have : {x | ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x y ≤ f x z}
      = ⋃ y, ({x | n = Encodable.encode y} ∩ {x | ∀ z, f x y ≤ f x z}) := by ext; simp
  rw [this]
  refine MeasurableSet.iUnion fun y ↦ (MeasurableSet.inter (by simp) ?_)
  exact measurableSet_isMin (by fun_prop) y

lemma isMinOn_measurableArgmin {α : Type*} [LinearOrder α]
    [Nonempty 𝓨] [Finite 𝓨] [Encodable 𝓨] [MeasurableSingletonClass 𝓨]
    [(x : ℕ) → Decidable (x ∈ Set.range (Encodable.encode (α := 𝓨)))]
    (f : 𝓧 → 𝓨 → α)
    [∀ x, DecidablePred fun n ↦ ∃ y, n = Encodable.encode y ∧ ∀ (z : 𝓨), f x y ≤ f x z]
    (x : 𝓧) (z : 𝓨) :
    f x (measurableArgmin f x) ≤ f x z := by
  obtain ⟨y, h_eq, h_le⟩ := Nat.find_spec (exists_isMinOn' f x)
  refine le_trans (le_of_eq ?_) (h_le z)
  rw [measurableArgmin, h_eq,
    MeasurableEmbedding.leftInverse_invFun (measurableEmbedding_encode 𝓨) y]

lemma hasGenBayesEstimator_of_finite [Nonempty 𝓨] [Finite 𝓨] [MeasurableSingletonClass 𝓨]
    (hl : Measurable (Function.uncurry ℓ)) :
    HasGenBayesEstimator ℓ P π where
  exists_isGenBayesEstimator := by
    classical
    have : Encodable 𝓨 := Encodable.ofCountable 𝓨
    have h_meas y : Measurable (fun x ↦ ∫⁻ θ, ℓ θ y ∂(P†π) x) :=
      (Measure.measurable_lintegral (by fun_prop)).comp (by fun_prop)
    refine ⟨measurableArgmin (fun x y ↦ ∫⁻ θ, ℓ θ y ∂(P†π) x),
      measurable_measurableArgmin h_meas, ae_of_all _ fun x ↦ ?_⟩
    have h := isMinOn_measurableArgmin (fun x y ↦ ∫⁻ θ, ℓ θ y ∂(P†π) x) x
    exact le_antisymm (by simpa using h) (iInf_le _ _)

end Finite

end ProbabilityTheory
