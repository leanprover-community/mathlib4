/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/

import Mathlib.Probability.Decision.Risk.Defs
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.WithDensity

/-!
# Basic properties of the risk of an estimator

## Main statements

* `bayesRisk_le_minimaxRisk`: the Bayes risk is less than or equal to the minimax risk.

Data-processing inequalities: if we compose the data generating kernel `P` with a Markov kernel
`η : Kernel 𝓧 𝓧'`, then the Bayes risk increases.
* `bayesRiskPrior_le_bayesRiskPrior_comp`: data-processing inequality for the Bayes risk
  with respect to a prior.
* `bayesRisk_le_bayesRisk_comp`: data-processing inequality for the Bayes risk.

## TODO

In many cases, the Bayes risk and the minimax risk are equal (by a so-called minimax theorem).

-/

open MeasureTheory Function
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ Θ' 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {mΘ' : MeasurableSpace Θ'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

section BayesRiskLeMinimaxRisk

lemma bayesianRisk_le_iSup_risk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesianRisk ℓ P κ π ≤ ⨆ θ, ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ) := lintegral_le_iSup _

lemma bayesRiskPrior_le_bayesianRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [hκ : IsMarkovKernel κ] :
    bayesRiskPrior ℓ P π ≤ bayesianRisk ℓ P κ π := iInf₂_le κ hκ

lemma bayesRiskPrior_le_bayesRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [hπ : IsProbabilityMeasure π] :
    bayesRiskPrior ℓ P π ≤ bayesRisk ℓ P := le_iSup₂ (f := fun π _ ↦ bayesRiskPrior ℓ P π) π hπ

lemma bayesRiskPrior_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesRiskPrior ℓ P π ≤ minimaxRisk ℓ P := iInf₂_mono fun _ _ ↦ bayesianRisk_le_iSup_risk _ _ _ _

/-- The Bayes risk is less than or equal to the minimax risk. -/
lemma bayesRisk_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) :
    bayesRisk ℓ P ≤ minimaxRisk ℓ P := iSup₂_le fun _ _ ↦ bayesRiskPrior_le_minimaxRisk _ _ _

end BayesRiskLeMinimaxRisk

section Const

/-- See `bayesianRisk_const_left` for a similar result with integrals swapped. -/
lemma bayesianRisk_const_left (ℓ : Θ → 𝓨 → ℝ≥0∞) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    bayesianRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₘ μ) ∂π := by
  simp [bayesianRisk]

/-- See `bayesianRisk_const_left'` for a similar result with integrals swapped. -/
lemma bayesianRisk_const_left' (hl : Measurable (uncurry ℓ)) (μ : Measure 𝓧) [SFinite μ]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [SFinite π] :
    bayesianRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ y, ∫⁻ θ, ℓ θ y ∂π ∂(κ ∘ₘ μ) := by
  rw [bayesianRisk_const_left, lintegral_lintegral_swap (by fun_prop)]

lemma bayesianRisk_const_right (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (ν : Measure 𝓨) (π : Measure Θ) :
    bayesianRisk ℓ P (Kernel.const 𝓧 ν) π = ∫⁻ θ, P θ .univ * ∫⁻ y, ℓ θ y ∂ν ∂π := by
  simp [bayesianRisk, Kernel.const_comp]

/-- See `bayesRiskPrior_le_iInf` for a simpler result when `P` is a Markov kernel. -/
lemma bayesRiskPrior_le_iInf' (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) (π : Measure Θ) :
    bayesRiskPrior ℓ P π ≤ ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y * P θ .univ ∂π := by
  simp_rw [le_iInf_iff, bayesRiskPrior]
  refine fun y ↦ iInf_le_of_le (Kernel.const _ (Measure.dirac y)) ?_
  simp only [iInf_pos, bayesianRisk_const_right, mul_comm]
  gcongr with θ
  rw [lintegral_dirac' _ (by fun_prop)]

/-- See `bayesRiskPrior_le_iInf'` for a similar result when `P` is not a Markov kernel. -/
lemma bayesRiskPrior_le_iInf (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (π : Measure Θ) :
    bayesRiskPrior ℓ P π ≤ ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂π :=
  (bayesRiskPrior_le_iInf' hl P π).trans_eq (by simp)

lemma bayesRiskPrior_const' (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [SFinite μ] (π : Measure Θ) [SFinite π]
    (hl_pos : μ .univ = ∞ → ⨅ y, ∫⁻ θ, ℓ θ y ∂π = 0 → ∃ y, ∫⁻ θ, ℓ θ y ∂π = 0)
    (h_zero : μ = 0 → Nonempty 𝓨) :
    bayesRiskPrior ℓ (Kernel.const Θ μ) π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y * μ .univ ∂π := by
  refine le_antisymm ((bayesRiskPrior_le_iInf' hl _ _).trans_eq (by simp)) ?_
  simp_rw [bayesRiskPrior, le_iInf_iff]
  intro κ hκ
  rw [bayesianRisk_const_left' hl]
  refine le_trans ?_ (iInf_mul_le_lintegral (fun y ↦ ∫⁻ θ, ℓ θ y ∂π))
  simp only [Measure.comp_apply_univ]
  rw [ENNReal.iInf_mul' hl_pos (fun hμ ↦ h_zero (by simpa using hμ))]
  gcongr with y
  rw [lintegral_mul_const]
  fun_prop

lemma bayesRiskPrior_const_of_neZero (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [NeZero μ] [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRiskPrior ℓ (Kernel.const Θ μ) π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y * μ .univ ∂π :=
  bayesRiskPrior_const' hl μ π (by simp) (by simp [NeZero.out])

lemma bayesRiskPrior_const_of_nonempty [Nonempty 𝓨] (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRiskPrior ℓ (Kernel.const Θ μ) π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y * μ .univ ∂π :=
  bayesRiskPrior_const' hl μ π (by simp) (fun _ ↦ inferInstance)

lemma bayesRiskPrior_const (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRiskPrior ℓ (Kernel.const Θ μ) π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂π := by
  simp [bayesRiskPrior_const_of_neZero hl μ π]

end Const

lemma bayesianRisk_le_mul' (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsFiniteKernel κ]
    (π : Measure Θ) {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesianRisk ℓ P κ π ≤ C * IsFiniteKernel.bound κ * IsFiniteKernel.bound P * π Set.univ := by
  rw [bayesianRisk]
  calc ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₖ P) θ ∂π
  _ ≤ ∫⁻ θ, ∫⁻ y, C ∂(κ ∘ₖ P) θ ∂π := by
    gcongr with θ y
    exact hℓC θ y
  _ = ∫⁻ θ, C * ∫⁻ x, κ x .univ ∂P θ ∂π := by simp [Kernel.comp_apply' _ _ _ .univ]
  _ ≤ ∫⁻ θ, C * ∫⁻ x, IsFiniteKernel.bound κ ∂P θ ∂π := by
    gcongr with θ x
    exact Kernel.measure_le_bound κ x Set.univ
  _ ≤ ∫⁻ θ, C * IsFiniteKernel.bound κ * IsFiniteKernel.bound P ∂π := by
    conv_lhs => simp only [lintegral_const, ← mul_assoc]
    gcongr with θ
    exact Kernel.measure_le_bound P θ Set.univ
  _ = C * IsFiniteKernel.bound κ * IsFiniteKernel.bound P * π Set.univ := by simp

-- todo : change `IsFiniteKernel.bound` to be the least upper bound, to reuse the previous lemma
lemma bayesianRisk_le_mul (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ]
    (π : Measure Θ) {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesianRisk ℓ P κ π ≤ C * IsFiniteKernel.bound P * π Set.univ := by
  rw [bayesianRisk]
  calc ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₖ P) θ ∂π
  _ ≤ ∫⁻ θ, ∫⁻ y, C ∂(κ ∘ₖ P) θ ∂π := by
    gcongr with θ y
    exact hℓC θ y
  _ = ∫⁻ θ, C * P θ .univ ∂π := by simp [Kernel.comp_apply' _ _ _ .univ]
  _ ≤ ∫⁻ θ, C * IsFiniteKernel.bound P ∂π := by
    conv_lhs => simp only [lintegral_const, ← mul_assoc]
    gcongr with θ
    exact Kernel.measure_le_bound P θ Set.univ
  _ = C * IsFiniteKernel.bound P * π Set.univ := by simp

lemma bayesRiskPrior_le_mul [h𝓨 : Nonempty 𝓨] (P : Kernel Θ 𝓧)
    [IsFiniteKernel P] (π : Measure Θ) {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesRiskPrior ℓ P π ≤ C * (IsFiniteKernel.bound P) * π Set.univ := by
  refine iInf₂_le_of_le (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) inferInstance ?_
  exact bayesianRisk_le_mul P (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) π hℓC

lemma bayesRisk_le_mul [h𝓨 : Nonempty 𝓨] (P : Kernel Θ 𝓧)
    [IsFiniteKernel P] {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesRisk ℓ P ≤ C * (IsFiniteKernel.bound P) :=
  iSup₂_le fun π hπ ↦ (bayesRiskPrior_le_mul P _ hℓC).trans_eq (by simp)

/-- For a bounded loss, the Bayes risk with respect to a prior is finite. -/
lemma bayesRiskPrior_lt_top [h𝓨 : Nonempty 𝓨] (P : Kernel Θ 𝓧)
    [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesRiskPrior ℓ P π < ∞ := by
  refine (bayesRiskPrior_le_mul P π hℓC).trans_lt ?_
  simp [ENNReal.mul_lt_top_iff, IsFiniteKernel.bound_lt_top P]

/-- For a bounded loss, the Bayes risk is finite. -/
lemma bayesRisk_lt_top [h𝓨 : Nonempty 𝓨] (P : Kernel Θ 𝓧)
    [IsFiniteKernel P] {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesRisk ℓ P < ∞ := by
  refine (bayesRisk_le_mul P hℓC).trans_lt ?_
  simp [ENNReal.mul_lt_top_iff, IsFiniteKernel.bound_lt_top P]

section Subsingleton

lemma bayesRiskPrior_discard (hl : Measurable (uncurry ℓ)) (π : Measure Θ) [SFinite π] :
    bayesRiskPrior ℓ (Kernel.discard Θ) π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂π := by
  rw [Kernel.discard_eq_const, bayesRiskPrior_const hl]

lemma bayesRiskPrior_eq_iInf_measure_of_subsingleton [Subsingleton 𝓧] [Nonempty 𝓨] :
    bayesRiskPrior ℓ P π
      = ⨅ (μ : Measure 𝓨) (_ : IsProbabilityMeasure μ), bayesianRisk ℓ P (Kernel.const 𝓧 μ) π := by
  rcases isEmpty_or_nonempty 𝓧 with hX | hX
  · simp [iInf_subtype']
  obtain x := Nonempty.some hX
  rw [bayesRiskPrior, iInf_subtype', iInf_subtype']
  let e : {κ : Kernel 𝓧 𝓨 // IsMarkovKernel κ} ≃ {μ : Measure 𝓨 // IsProbabilityMeasure μ} :=
    { toFun κ := ⟨κ.1 x, by have := κ.2.isProbabilityMeasure x; infer_instance⟩
      invFun μ := ⟨Kernel.const 𝓧 μ, by have := μ.2; infer_instance⟩
      left_inv κ := by ext y; simp only [Kernel.const_apply, Subsingleton.elim x y]
      right_inv μ := by simp }
  rw [← Equiv.iInf_comp e.symm]
  congr

lemma bayesRiskPrior_of_subsingleton' [Subsingleton 𝓧] [Nonempty 𝓨] [SFinite π]
    (hl : Measurable (uncurry ℓ)) :
    bayesRiskPrior ℓ P π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y * P θ .univ ∂π := by
  refine le_antisymm (bayesRiskPrior_le_iInf' hl _ _) ?_
  rw [bayesRiskPrior_eq_iInf_measure_of_subsingleton]
  simp only [bayesianRisk_const_right, le_iInf_iff]
  refine fun μ hμ ↦ (iInf_le_lintegral (μ := μ) _).trans_eq ?_
  rw [lintegral_lintegral_swap]
  · congr with θ
    rw [lintegral_mul_const _ (by fun_prop), mul_comm]
  · have := P.measurable_coe .univ
    fun_prop

lemma bayesRiskPrior_of_subsingleton [Subsingleton 𝓧] [Nonempty 𝓨] [IsMarkovKernel P] [SFinite π]
    (hl : Measurable (uncurry ℓ)) :
    bayesRiskPrior ℓ P π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂π := by
  simp [bayesRiskPrior_of_subsingleton' hl]

lemma bayesRiskPrior_eq_bayesRiskPrior_discard_of_subsingleton [Subsingleton 𝓧] [Nonempty 𝓨]
    [IsMarkovKernel P] [SFinite π] (hl : Measurable (uncurry ℓ)) :
    bayesRiskPrior ℓ P π = bayesRiskPrior ℓ (Kernel.discard Θ) π := by
  simp [bayesRiskPrior_of_subsingleton hl]

end Subsingleton

lemma bayesianRisk_withDensity (hl : Measurable (uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsSFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ]
    (π : Measure Θ) {f : Θ → ℝ≥0∞} (hf : Measurable f) :
    bayesianRisk ℓ (P.withDensity (fun θ _ ↦ f θ)) κ π = bayesianRisk ℓ P κ (π.withDensity f) := by
  simp only [bayesianRisk]
  rw [lintegral_withDensity_eq_lintegral_mul _ hf (by fun_prop)]
  congr with θ
  rw [Kernel.comp_apply, Kernel.withDensity_apply _ (by fun_prop), Pi.mul_apply, Kernel.comp_apply]
  simp

lemma bayesRiskPrior_withDensity (hl : Measurable (uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsSFiniteKernel P] (π : Measure Θ)
    {f : Θ → ℝ≥0∞} (hf : Measurable f) :
    bayesRiskPrior ℓ (P.withDensity (fun θ _ ↦ f θ)) π = bayesRiskPrior ℓ P (π.withDensity f) := by
  simp_rw [bayesRiskPrior]
  congr! 3 with κ hκ
  rw [bayesianRisk_withDensity hl P κ π hf]

section Compositions

/-- **Data processing inequality** for the Bayes risk with respect to a prior: composition of the
data generating kernel by a Markov kernel increases the risk. -/
lemma bayesRiskPrior_le_bayesRiskPrior_comp (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    bayesRiskPrior ℓ P π ≤ bayesRiskPrior ℓ (η ∘ₖ P) π := by
  simp only [bayesRiskPrior, bayesianRisk, le_iInf_iff]
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

/-- **Data processing inequality** for the Bayes risk: composition of the
data generating kernel by a Markov kernel increases the risk. -/
lemma bayesRisk_le_bayesRisk_comp (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    bayesRisk ℓ P ≤ bayesRisk ℓ (η ∘ₖ P) :=
  iSup₂_mono fun _ _ ↦ bayesRiskPrior_le_bayesRiskPrior_comp _ _ _ _

lemma bayesRisk_compProd_le_bayesRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (η : Kernel (Θ × 𝓧) 𝓧') [IsMarkovKernel η] :
    bayesRisk ℓ (P ⊗ₖ η) ≤ bayesRisk ℓ P :=
  iSup₂_mono fun _ _ ↦ bayesRiskPrior_compProd_le_bayesRiskPrior _ _ _ _

lemma bayesianRisk_comap_measurableEquiv (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) (e : Θ' ≃ᵐ Θ) :
    bayesianRisk (fun θ ↦ ℓ (e θ)) (P.comap e e.measurable) κ (π.comap e)
      = bayesianRisk ℓ P κ π := by
  simp only [bayesianRisk]
  rw [← MeasurableEquiv.map_symm, lintegral_map (by fun_prop) e.symm.measurable]
  congr with θ
  congr
  · ext s hs
    simp [κ.comp_apply' _ _ hs, Kernel.comap_apply]
  · simp

lemma bayesRiskPrior_comap_measurableEquiv (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (π : Measure Θ) (e : Θ' ≃ᵐ Θ) :
    bayesRiskPrior (fun θ ↦ ℓ (e θ)) (P.comap e e.measurable) (π.comap e)
      = bayesRiskPrior ℓ P π := by
  simp only [bayesRiskPrior, bayesianRisk_comap_measurableEquiv hl P _ π e]

end Compositions

end ProbabilityTheory
