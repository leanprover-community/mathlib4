/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/

import Mathlib.Probability.Kernel.Posterior

/-!
# Risk of an estimator

An estimation problem is defined by a parameter space `Θ`, a data generating kernel `P : Kernel Θ 𝓧`
and a loss function `ℓ : Θ → 𝓨 → ℝ≥0∞`.
A (randomized) estimator is a kernel `κ : Kernel 𝓧 𝓨` that maps data to estimates of a quantity
of interest that depends on the parameter. Often the quantity of interest is the parameter itself
and `𝓨 = Θ`.
The quality of an estimate `y` when data comes from the distribution with parameter `θ` is measured
by the loss function `ℓ θ z`.

## Main definitions

* `risk ℓ P κ θ`
* `bayesianRisk ℓ P κ π`
* `bayesRiskPrior ℓ P π`
* `bayesRisk ℓ P`

## Main statements

* `fooBar_unique`

## Implementation details


-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ Θ' 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {mΘ' : MeasurableSpace Θ'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

section Definitions

/-- The risk of an estimator `κ` on an estimation task with loss `ℓ` and data generating kernel `P`
at the parameter `θ`. -/
noncomputable
def risk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (θ : Θ) : ℝ≥0∞ :=
  ∫⁻ z, ℓ θ z ∂((κ ∘ₖ P) θ)

/-- The bayesian risk of an estimator `κ` on an estimation task with loss `ℓ` and
data generating kernel `P` with respect to a prior `π`. -/
noncomputable
def bayesianRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) : ℝ≥0∞ :=
  ∫⁻ θ, risk ℓ P κ θ ∂π

/-- The Bayes risk with respect to a prior `π`, defined as the infimum of the Bayesian risks of all
estimators. -/
noncomputable
def bayesRiskPrior {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (π : Measure Θ) : ℝ≥0∞ :=
  ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), bayesianRisk ℓ P κ π

/-- The Bayes risk, defined as the supremum over priors of the Bayes risk with respect to
the prior. -/
noncomputable
def bayesRisk {𝓨 : Type*} [MeasurableSpace 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) : ℝ≥0∞ :=
  ⨆ (π : Measure Θ) (_ : IsProbabilityMeasure π), bayesRiskPrior ℓ P π

/-- The minimax risk, defined as the infimum over estimators of the maximal risk of
the estimator. -/
noncomputable
def minimaxRisk {𝓨 : Type*} [MeasurableSpace 𝓨] (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) : ℝ≥0∞ :=
  ⨅ (κ : Kernel 𝓧 𝓨) (_ : IsMarkovKernel κ), ⨆ θ, risk ℓ P κ θ

end Definitions

@[simp]
lemma bayesianRisk_of_isEmpty [IsEmpty Θ] : bayesianRisk ℓ P κ π = 0 := by simp [bayesianRisk]

lemma bayesianRisk_le_iSup_risk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesianRisk ℓ P κ π ≤ ⨆ θ, risk ℓ P κ θ := by
  rw [bayesianRisk]
  calc ∫⁻ θ, risk ℓ P κ θ ∂π
  _ ≤ ∫⁻ _, (⨆ θ', risk ℓ P κ θ') ∂π := lintegral_mono (fun θ ↦ le_iSup _ _)
  _ = ⨆ θ, risk ℓ P κ θ := by simp

lemma bayesianRisk_comap_measurableEquiv (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) (e : Θ ≃ᵐ Θ') :
    bayesianRisk (fun θ z ↦ ℓ (e.symm θ) z) (P.comap e.symm e.symm.measurable)
      κ (π.map e) = bayesianRisk ℓ P κ π := by
  simp only [bayesianRisk, risk]
  rw [lintegral_map _ e.measurable]
  · congr with θ
    congr
    · ext z hz
      simp [κ.comp_apply' _ _ hz, Kernel.comap_apply]
    · simp
  · fun_prop

/-- **Data processing inequality** for the Bayes risk with respect to a prior. -/
lemma bayesRiskPrior_le_bayesRiskPrior_comp (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    bayesRiskPrior ℓ P π ≤ bayesRiskPrior ℓ (η ∘ₖ P) π := by
  simp only [bayesRiskPrior, bayesianRisk, risk, le_iInf_iff]
  intro κ hκ
  rw [← κ.comp_assoc η]
  exact iInf_le_of_le (κ ∘ₖ η) (iInf_le_of_le inferInstance le_rfl)

/-- An estimator is a Bayes estimator for a prior `π` if it attains the Bayes risk for `π`. -/
def IsBayesEstimator (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) : Prop :=
  bayesianRisk ℓ P κ π = bayesRiskPrior ℓ P π

lemma bayesRiskPrior_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesRiskPrior ℓ P π ≤ minimaxRisk ℓ P :=
  iInf_mono (fun _ ↦ iInf_mono fun _ ↦ bayesianRisk_le_iSup_risk _ _ _ _)

lemma bayesRisk_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) :
    bayesRisk ℓ P ≤ minimaxRisk ℓ P := by
  simp only [bayesRisk, iSup_le_iff]
  exact fun _ _ ↦ bayesRiskPrior_le_minimaxRisk _ _ _

/-! ### Properties of the Bayes risk of a prior -/

lemma bayesRiskPrior_compProd_le_bayesRiskPrior (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (π : Measure Θ) (κ : Kernel (Θ × 𝓧) 𝓧') [IsMarkovKernel κ] :
    bayesRiskPrior ℓ (P ⊗ₖ κ) π ≤ bayesRiskPrior ℓ P π := by
  have : P = (Kernel.deterministic Prod.fst (by fun_prop)) ∘ₖ (P ⊗ₖ κ) := by
    rw [Kernel.deterministic_comp_eq_map, ← Kernel.fst_eq, Kernel.fst_compProd]
  nth_rw 2 [this]
  exact bayesRiskPrior_le_bayesRiskPrior_comp _ _ _ _

-- Do we also need a version without the `IsMarkovKernel` assumption? it would be of the form:
-- `bayesRiskPrior E π ≤ ⨅ z : 𝓨, ∫⁻ θ, E.ℓ (E.y θ, z) * (E.P θ) .univ ∂π`
lemma bayesRiskPrior_le_inf (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [IsMarkovKernel P] :
    bayesRiskPrior ℓ P π ≤ ⨅ z : 𝓨, ∫⁻ θ, ℓ θ z ∂π := by
  simp_rw [le_iInf_iff, bayesRiskPrior]
  refine fun z ↦ iInf_le_of_le (Kernel.const _ (Measure.dirac z)) ?_
  convert iInf_le _ ?_ using 1
  · simp_rw [bayesianRisk, risk, Kernel.const_comp', Kernel.const_apply]
    congr with θ
    rw [lintegral_dirac']
    fun_prop
  · infer_instance

/-- The Bayesian risk of an estimator `κ` with respect to a prior `π` can be expressed as
an integral in the following way: `R_π(κ) = ((P†π × κ) ∘ P ∘ π)[(θ, z) ↦ ℓ(y(θ), z)]`. -/
lemma bayesianRisk_eq_lintegral_bayesInv_prod [StandardBorelSpace Θ] [Nonempty Θ]
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] [IsSFiniteKernel κ] :
    bayesianRisk ℓ P κ π = ∫⁻ (θz : Θ × 𝓨), ℓ θz.1 θz.2 ∂(((P†π) ×ₖ κ) ∘ₘ (P ∘ₘ π)) := by
  simp only [bayesianRisk, risk]
  rw [← Measure.lintegral_compProd (f := fun θz ↦ ℓ θz.1 θz.2) (by fun_prop)]
  congr
  calc π ⊗ₘ (κ ∘ₖ P) = (Kernel.id ∥ₖ κ) ∘ₘ (π ⊗ₘ P) := Measure.parallelComp_comp_compProd.symm
  _ = (Kernel.id ∥ₖ κ) ∘ₘ ((P†π) ×ₖ Kernel.id) ∘ₘ P ∘ₘ π := by rw [posterior_prod_id_comp]
  _ = ((P†π) ×ₖ κ) ∘ₘ P ∘ₘ π := by
      rw [Measure.comp_assoc, Kernel.parallelComp_comp_prod, Kernel.id_comp, Kernel.comp_id]

lemma bayesianRisk_eq_integral_integral_integral [StandardBorelSpace Θ] [Nonempty Θ]
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] [IsSFiniteKernel κ] :
    bayesianRisk ℓ P κ π = ∫⁻ x, ∫⁻ z, ∫⁻ θ, ℓ θ z ∂(P†π) x ∂κ x ∂(P ∘ₘ π) := by
  rw [bayesianRisk_eq_lintegral_bayesInv_prod hl,
    Measure.lintegral_bind ((P†π) ×ₖ κ).aemeasurable (by fun_prop)]
  congr with x
  rw [Kernel.prod_apply, lintegral_prod_symm' _ (by fun_prop)]

lemma bayesianRisk_ge_lintegral_iInf_bayesInv [StandardBorelSpace Θ] [Nonempty Θ]
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] [IsMarkovKernel κ] :
    bayesianRisk ℓ P κ π ≥ ∫⁻ x, ⨅ z : 𝓨, ∫⁻ θ, ℓ θ z ∂((P†π) x) ∂(P ∘ₘ π) := by
  rw [bayesianRisk_eq_integral_integral_integral hl]
  gcongr with x
  calc
    _ ≥ ∫⁻ _, ⨅ z, ∫⁻ (θ : Θ), ℓ θ z ∂(P†π) x ∂κ x := lintegral_mono fun z ↦ iInf_le _ z
    _ = ⨅ z, ∫⁻ (θ : Θ), ℓ θ z ∂(P†π) x := by rw [lintegral_const, measure_univ, mul_one]

section IsGenBayesEstimator

/-! ### Generalized Bayes estimator -/

variable [StandardBorelSpace Θ] [Nonempty Θ] {f : 𝓧 → 𝓨}
  [IsFiniteKernel P] [IsFiniteMeasure π]

/-- We say that a measurable function `f : 𝓧 → 𝓨` is a Generalized Bayes estimator for the
estimation problem `E` with respect to the prior `π` if for `(P ∘ₘ π)`-almost every `x` it is of
the form `x ↦ argmin_z P†π(x)[θ ↦ ℓ(y(θ), z)]`. -/
structure IsGenBayesEstimator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (f : 𝓧 → 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] : Prop where
  measurable : Measurable f
  property : ∀ᵐ x ∂(P ∘ₘ π), ∫⁻ θ, ℓ θ (f x) ∂(P†π) x
    = ⨅ z, ∫⁻ θ, ℓ θ z ∂(P†π) x

/-- Given a Generalized Bayes estimator `f`, we can define a deterministic kernel. -/
noncomputable
abbrev IsGenBayesEstimator.kernel (h : IsGenBayesEstimator ℓ P f π) : Kernel 𝓧 𝓨 :=
  Kernel.deterministic f h.measurable

lemma IsGenBayesEstimator.bayesianRisk_eq_integral_iInf (hf : IsGenBayesEstimator ℓ P f π)
    (hl : Measurable (Function.uncurry ℓ)) :
    bayesianRisk ℓ P hf.kernel π = ∫⁻ x, ⨅ z, ∫⁻ θ, ℓ θ z ∂(P†π) x ∂(P ∘ₘ π) := by
  rw [bayesianRisk_eq_integral_integral_integral hl]
  refine lintegral_congr_ae ?_
  filter_upwards [hf.property] with x hx
  rwa [Kernel.deterministic_apply,
    lintegral_dirac' _ (Measurable.lintegral_prod_left (by fun_prop))]

/-- A generalized Bayes estimator is a Bayes estimator: that is, it minimizes the Bayesian risk. -/
lemma IsGenBayesEstimator.isBayesEstimator (hf : IsGenBayesEstimator ℓ P f π)
    (hl : Measurable (Function.uncurry ℓ)) :
    IsBayesEstimator ℓ P hf.kernel π := by
  simp_rw [IsBayesEstimator, bayesRiskPrior]
  apply le_antisymm
  · rw [hf.bayesianRisk_eq_integral_iInf hl]
    simp_all [bayesianRisk_ge_lintegral_iInf_bayesInv]
  · refine iInf_le_of_le hf.kernel ?_
    exact iInf_le _ (Kernel.isMarkovKernel_deterministic hf.measurable)

/-- The estimation problem admits a Generalized Bayes estimator with respect to the prior `π`. -/
class HasGenBayesEstimator {𝓨 : Type*} [MeasurableSpace 𝓨]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] where
  /-- The Generalized Bayes estimator. -/
  estimator : 𝓧 → 𝓨
  isGenBayesEstimator : IsGenBayesEstimator ℓ P estimator π

lemma bayesRiskPrior_eq_of_hasGenBayesEstimator
    (hl : Measurable (Function.uncurry ℓ)) [h : HasGenBayesEstimator ℓ P π] :
    bayesRiskPrior ℓ P π = ∫⁻ x, ⨅ z, ∫⁻ θ, ℓ θ z ∂((P†π) x) ∂(P ∘ₘ π) := by
  rw [← h.isGenBayesEstimator.isBayesEstimator hl,
    IsGenBayesEstimator.bayesianRisk_eq_integral_iInf _ hl]

end IsGenBayesEstimator

end ProbabilityTheory
