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

lemma iInf_mul_le_lintegral {α : Type*} {_ : MeasurableSpace α} (μ : Measure α) (f : α → ℝ≥0∞) :
    (⨅ x, f x) * μ .univ ≤ ∫⁻ x, f x ∂μ := by
  have : (⨅ x, f x) * μ .univ = ∫⁻ y, ⨅ x, f x ∂μ := by simp
  rw [this]
  gcongr
  exact iInf_le _ _

lemma iInf_le_lintegral {α : Type*} {_ : MeasurableSpace α} (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ≥0∞) :
    ⨅ x, f x ≤ ∫⁻ x, f x ∂μ :=
  le_trans (by simp) (iInf_mul_le_lintegral μ f)

namespace ProbabilityTheory

@[simp]
lemma Kernel.comp_const {α β γ : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    {_ : MeasurableSpace γ}
    (κ : Kernel β γ) (μ : Measure β) : κ ∘ₖ Kernel.const α μ = Kernel.const α (κ ∘ₘ μ) := by
  ext x s hs
  rw [Kernel.comp_apply, Measure.bind_apply hs (by fun_prop), Kernel.const_apply,
    Kernel.const_apply, Measure.bind_apply hs (by fun_prop)]

variable {Θ Θ' 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {mΘ' : MeasurableSpace Θ'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

instance [Nonempty 𝓨] : Nonempty (Subtype (@IsMarkovKernel 𝓧 𝓨 m𝓧 m𝓨)) := by
  simp only [nonempty_subtype]
  let y : 𝓨 := Classical.ofNonempty
  exact ⟨Kernel.const _ (Measure.dirac y), inferInstance⟩

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

section Zero

@[simp]
lemma risk_zero_left (ℓ : Θ → 𝓨 → ℝ≥0∞) (κ : Kernel 𝓧 𝓨) (θ : Θ) :
    risk ℓ (0 : Kernel Θ 𝓧) κ θ = 0 := by simp [risk]

@[simp]
lemma risk_zero_right (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (θ : Θ) :
    risk ℓ P (0 : Kernel 𝓧 𝓨) θ = 0 := by simp [risk]

@[simp]
lemma bayesianRisk_zero_left (ℓ : Θ → 𝓨 → ℝ≥0∞) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    bayesianRisk ℓ (0 : Kernel Θ 𝓧) κ π = 0 := by simp [bayesianRisk]

@[simp]
lemma bayesianRisk_zero_right (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (π : Measure Θ) :
    bayesianRisk ℓ P (0 : Kernel 𝓧 𝓨) π = 0 := by simp [bayesianRisk]

@[simp]
lemma bayesianRisk_zero_prior (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) :
    bayesianRisk ℓ P κ 0 = 0 := by simp [bayesianRisk]

@[simp]
lemma bayesRiskPrior_zero_left (ℓ : Θ → 𝓨 → ℝ≥0∞) (π : Measure Θ) [Nonempty 𝓨] :
    bayesRiskPrior ℓ (0 : Kernel Θ 𝓧) π = 0 := by
  simp only [bayesRiskPrior, bayesianRisk_zero_left]
  rw [iInf_subtype']
  simp

lemma bayesRiskPrior_zero_right (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [Nonempty 𝓨] :
    bayesRiskPrior ℓ P (0 : Measure Θ) = 0 := by
  simp only [bayesRiskPrior, bayesianRisk_zero_prior]
  rw [iInf_subtype']
  simp

end Zero

section Const

lemma risk_const (ℓ : Θ → 𝓨 → ℝ≥0∞) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (θ : Θ) :
    risk ℓ (Kernel.const Θ μ) κ θ = ∫⁻ z, ℓ θ z ∂(κ ∘ₘ μ) := by simp [risk]

lemma risk_const_right (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (ν : Measure 𝓨) (θ : Θ) :
    risk ℓ P (Kernel.const 𝓧 ν) θ = P θ .univ * ∫⁻ z, ℓ θ z ∂ν := by simp [risk, Kernel.const_comp]

lemma bayesianRisk_const (ℓ : Θ → 𝓨 → ℝ≥0∞) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    bayesianRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ θ, ∫⁻ z, ℓ θ z ∂(κ ∘ₘ μ) ∂π := by
  simp [bayesianRisk, risk]

lemma bayesianRisk_const' (hl : Measurable (Function.uncurry ℓ)) (μ : Measure 𝓧) [SFinite μ]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [SFinite π] :
    bayesianRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ z, ∫⁻ θ, ℓ θ z ∂π ∂(κ ∘ₘ μ) := by
  rw [bayesianRisk_const, lintegral_lintegral_swap (by fun_prop)]

lemma bayesianRisk_const_right (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (ν : Measure 𝓨) (π : Measure Θ) :
    bayesianRisk ℓ P (Kernel.const 𝓧 ν) π = ∫⁻ θ, P θ .univ * ∫⁻ z, ℓ θ z ∂ν ∂π := by
  simp only [bayesianRisk, risk_const_right]

lemma bayesRiskPrior_le_inf' (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧)
    (π : Measure Θ) :
    bayesRiskPrior ℓ P π ≤ ⨅ z : 𝓨, ∫⁻ θ, ℓ θ z * P θ .univ ∂π := by
  simp_rw [le_iInf_iff, bayesRiskPrior]
  refine fun z ↦ iInf_le_of_le (Kernel.const _ (Measure.dirac z)) ?_
  simp only [iInf_pos, bayesianRisk_const_right, mul_comm]
  gcongr with θ
  rw [lintegral_dirac' _ (by fun_prop)]

lemma bayesRiskPrior_le_inf (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [IsMarkovKernel P] :
    bayesRiskPrior ℓ P π ≤ ⨅ z : 𝓨, ∫⁻ θ, ℓ θ z ∂π :=
  (bayesRiskPrior_le_inf' hl P π).trans_eq (by simp)

lemma bayesRiskPrior_const''' (hl : Measurable (Function.uncurry ℓ))
    (μ : Measure 𝓧) [SFinite μ] (π : Measure Θ) [SFinite π]
    (hl_pos : μ .univ = ∞ → ⨅ z, ∫⁻ θ, ℓ θ z ∂π = 0 → ∃ z, ∫⁻ θ, ℓ θ z ∂π = 0)
    (h_zero : μ = 0 → Nonempty 𝓨) :
    bayesRiskPrior ℓ (Kernel.const Θ μ) π = ⨅ z : 𝓨, ∫⁻ θ, ℓ θ z * μ .univ ∂π := by
  refine le_antisymm ?_ ?_
  · exact (bayesRiskPrior_le_inf' hl _ _).trans_eq (by simp)
  · simp_rw [bayesRiskPrior, le_iInf_iff]
    intro κ hκ
    rw [bayesianRisk_const' hl]
    refine le_trans ?_ (iInf_mul_le_lintegral (κ ∘ₘ μ) (fun z ↦ ∫⁻ θ, ℓ θ z ∂π))
    simp only [Measure.comp_apply_univ]
    rw [ENNReal.iInf_mul' hl_pos (fun hμ ↦ h_zero (by simpa using hμ))]
    gcongr with z
    rw [lintegral_mul_const]
    fun_prop

lemma bayesRiskPrior_const'' (hl : Measurable (Function.uncurry ℓ))
    (μ : Measure 𝓧) [NeZero μ] [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRiskPrior ℓ (Kernel.const Θ μ) π = ⨅ z : 𝓨, ∫⁻ θ, ℓ θ z * μ .univ ∂π :=
  bayesRiskPrior_const''' hl μ π (by simp) (by simp [NeZero.out])

lemma bayesRiskPrior_const' [Nonempty 𝓨] (hl : Measurable (Function.uncurry ℓ))
    (μ : Measure 𝓧) [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRiskPrior ℓ (Kernel.const Θ μ) π = ⨅ z : 𝓨, ∫⁻ θ, ℓ θ z * μ .univ ∂π :=
  bayesRiskPrior_const''' hl μ π (by simp) (fun _ ↦ inferInstance)

lemma bayesRiskPrior_const (hl : Measurable (Function.uncurry ℓ))
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRiskPrior ℓ (Kernel.const Θ μ) π = ⨅ z : 𝓨, ∫⁻ θ, ℓ θ z ∂π := by
  simp [bayesRiskPrior_const'' hl μ π]

end Const

section BayesRiskLeMinimaxRisk

lemma bayesianRisk_le_iSup_risk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesianRisk ℓ P κ π ≤ ⨆ θ, risk ℓ P κ θ := by
  rw [bayesianRisk]
  calc ∫⁻ θ, risk ℓ P κ θ ∂π
  _ ≤ ∫⁻ _, (⨆ θ', risk ℓ P κ θ') ∂π := lintegral_mono (fun θ ↦ le_iSup _ _)
  _ = ⨆ θ, risk ℓ P κ θ := by simp

lemma bayesRiskPrior_le_bayesianRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [hκ : IsMarkovKernel κ] :
    bayesRiskPrior ℓ P π ≤ bayesianRisk ℓ P κ π := by
  simp only [bayesRiskPrior]
  exact iInf₂_le κ hκ

lemma bayesRiskPrior_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesRiskPrior ℓ P π ≤ minimaxRisk ℓ P :=
  iInf_mono (fun _ ↦ iInf_mono fun _ ↦ bayesianRisk_le_iSup_risk _ _ _ _)

lemma bayesRisk_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) :
    bayesRisk ℓ P ≤ minimaxRisk ℓ P := by
  simp only [bayesRisk, iSup_le_iff]
  exact fun _ _ ↦ bayesRiskPrior_le_minimaxRisk _ _ _

end BayesRiskLeMinimaxRisk

section Compositions

/-- **Data processing inequality** for the Bayes risk with respect to a prior: composition of the
data generating kernel by a Markov kernel increases the risk. -/
lemma bayesRiskPrior_le_bayesRiskPrior_comp (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    bayesRiskPrior ℓ P π ≤ bayesRiskPrior ℓ (η ∘ₖ P) π := by
  simp only [bayesRiskPrior, bayesianRisk, risk, le_iInf_iff]
  intro κ hκ
  rw [← κ.comp_assoc η]
  exact iInf_le_of_le (κ ∘ₖ η) (iInf_le_of_le inferInstance le_rfl)

lemma bayesRiskPrior_compProd_le_bayesRiskPrior (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (π : Measure Θ) (η : Kernel (Θ × 𝓧) 𝓧') [IsMarkovKernel η] :
    bayesRiskPrior ℓ (P ⊗ₖ η) π ≤ bayesRiskPrior ℓ P π := by
  have : P = (Kernel.deterministic Prod.fst (by fun_prop)) ∘ₖ (P ⊗ₖ η) := by
    rw [Kernel.deterministic_comp_eq_map, ← Kernel.fst_eq, Kernel.fst_compProd]
  conv_rhs => rw [this]
  exact bayesRiskPrior_le_bayesRiskPrior_comp _ _ _ _

lemma bayesianRisk_comap_measurableEquiv (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) (e : Θ' ≃ᵐ Θ) :
    bayesianRisk (fun θ z ↦ ℓ (e θ) z) (P.comap e e.measurable) κ (π.comap e)
      = bayesianRisk ℓ P κ π := by
  simp only [bayesianRisk, risk]
  rw [← MeasurableEquiv.map_symm, lintegral_map (by fun_prop) e.symm.measurable]
  congr with θ
  congr
  · ext z hz
    simp [κ.comp_apply' _ _ hz, Kernel.comap_apply]
  · simp

end Compositions

section Posterior

variable [StandardBorelSpace Θ] [Nonempty Θ]

/-- The Bayesian risk of an estimator `κ` with respect to a prior `π` can be expressed as
an integral in the following way: `R_π(κ) = ((P†π × κ) ∘ P ∘ π)[(θ, z) ↦ ℓ(y(θ), z)]`. -/
lemma bayesianRisk_eq_lintegral_posterior_prod
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

lemma bayesianRisk_eq_lintegral_lintegral_lintegral
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] [IsSFiniteKernel κ] :
    bayesianRisk ℓ P κ π = ∫⁻ x, ∫⁻ z, ∫⁻ θ, ℓ θ z ∂(P†π) x ∂κ x ∂(P ∘ₘ π) := by
  rw [bayesianRisk_eq_lintegral_posterior_prod hl,
    Measure.lintegral_bind ((P†π) ×ₖ κ).aemeasurable (by fun_prop)]
  congr with x
  rw [Kernel.prod_apply, lintegral_prod_symm' _ (by fun_prop)]

lemma lintegral_iInf_posterior_le_bayesianRisk
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsFiniteMeasure π] [IsMarkovKernel κ] :
    ∫⁻ x, ⨅ z : 𝓨, ∫⁻ θ, ℓ θ z ∂((P†π) x) ∂(P ∘ₘ π) ≤ bayesianRisk ℓ P κ π := by
  rw [bayesianRisk_eq_lintegral_lintegral_lintegral hl]
  gcongr with x
  exact iInf_le_lintegral _ _

lemma lintegral_iInf_posterior_le_bayesRiskPrior
    (hl : Measurable (Function.uncurry ℓ)) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π] :
    ∫⁻ x, ⨅ z : 𝓨, ∫⁻ θ, ℓ θ z ∂((P†π) x) ∂(P ∘ₘ π) ≤ bayesRiskPrior ℓ P π := by
  simp only [bayesRiskPrior, le_iInf_iff]
  exact fun κ _ ↦ lintegral_iInf_posterior_le_bayesianRisk hl P κ π

end Posterior

end ProbabilityTheory
