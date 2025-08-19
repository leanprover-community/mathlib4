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

* `iSup_bayesRisk_le_minimaxRisk`: the maximal Bayes risk is less than or equal to the minimax risk.

Data-processing inequalities: if we compose the data generating kernel `P` with a Markov kernel
`η : Kernel 𝓧 𝓧'`, then the Bayes risk increases.
* `bayesRisk_le_bayesRisk_comp`: data-processing inequality for the Bayes risk
  with respect to a prior.
* `supBayesRisk_le_supBayesRisk_comp`: data-processing inequality for the supremum of
  the Bayes risk.

## TODO

In many cases, the maximal Bayes risk and the minimax risk are equal
(by a so-called minimax theorem).

-/

open MeasureTheory Function
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ Θ' 𝓧 𝓧' 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {mΘ' : MeasurableSpace Θ'}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓧' : MeasurableSpace 𝓧'} {m𝓨 : MeasurableSpace 𝓨}
  {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧} {κ : Kernel 𝓧 𝓨} {π : Measure Θ}

section BayesRiskLeMinimaxRisk

lemma avgRisk_le_iSup_risk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    avgRisk ℓ P κ π ≤ ⨆ θ, ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ) := lintegral_le_iSup _

lemma bayesRisk_le_avgRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) [hκ : IsMarkovKernel κ] :
    bayesRisk ℓ P π ≤ avgRisk ℓ P κ π := iInf₂_le κ hκ

lemma bayesRisk_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [IsProbabilityMeasure π] :
    bayesRisk ℓ P π ≤ minimaxRisk ℓ P := iInf₂_mono fun _ _ ↦ avgRisk_le_iSup_risk _ _ _ _

/-- The maximal Bayes risk is less than or equal to the minimax risk. -/
lemma iSup_bayesRisk_le_minimaxRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) :
    ⨆ (π : Measure Θ) (_ : IsProbabilityMeasure π), bayesRisk ℓ P π
     ≤ minimaxRisk ℓ P := iSup₂_le fun _ _ ↦ bayesRisk_le_minimaxRisk _ _ _

end BayesRiskLeMinimaxRisk

section Const

/-- See `avgRisk_const_left` for a similar result with integrals swapped. -/
lemma avgRisk_const_left (ℓ : Θ → 𝓨 → ℝ≥0∞) (μ : Measure 𝓧) (κ : Kernel 𝓧 𝓨) (π : Measure Θ) :
    avgRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ θ, ∫⁻ y, ℓ θ y ∂(κ ∘ₘ μ) ∂π := by
  simp [avgRisk]

/-- See `avgRisk_const_left'` for a similar result with integrals swapped. -/
lemma avgRisk_const_left' (hl : Measurable (uncurry ℓ)) (μ : Measure 𝓧) [SFinite μ]
    (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) [SFinite π] :
    avgRisk ℓ (Kernel.const Θ μ) κ π = ∫⁻ y, ∫⁻ θ, ℓ θ y ∂π ∂(κ ∘ₘ μ) := by
  rw [avgRisk_const_left, lintegral_lintegral_swap (by fun_prop)]

lemma avgRisk_const_right (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (ν : Measure 𝓨) (π : Measure Θ) :
    avgRisk ℓ P (Kernel.const 𝓧 ν) π = ∫⁻ θ, P θ .univ * ∫⁻ y, ℓ θ y ∂ν ∂π := by
  simp [avgRisk, Kernel.const_comp]

/-- See `bayesRisk_le_iInf` for a simpler result when `P` is a Markov kernel. -/
lemma bayesRisk_le_iInf' (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) (π : Measure Θ) :
    bayesRisk ℓ P π ≤ ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y * P θ .univ ∂π := by
  simp_rw [le_iInf_iff, bayesRisk]
  refine fun y ↦ iInf_le_of_le (Kernel.const _ (Measure.dirac y)) ?_
  simp only [iInf_pos, avgRisk_const_right, mul_comm]
  gcongr with θ
  rw [lintegral_dirac' _ (by fun_prop)]

/-- See `bayesRisk_le_iInf'` for a similar result when `P` is not a Markov kernel. -/
lemma bayesRisk_le_iInf (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (π : Measure Θ) :
    bayesRisk ℓ P π ≤ ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂π :=
  (bayesRisk_le_iInf' hl P π).trans_eq (by simp)

lemma bayesRisk_const' (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [SFinite μ] (π : Measure Θ) [SFinite π]
    (hl_pos : μ .univ = ∞ → ⨅ y, ∫⁻ θ, ℓ θ y ∂π = 0 → ∃ y, ∫⁻ θ, ℓ θ y ∂π = 0)
    (h_zero : μ = 0 → Nonempty 𝓨) :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y * μ .univ ∂π := by
  refine le_antisymm ((bayesRisk_le_iInf' hl _ _).trans_eq (by simp)) ?_
  simp_rw [bayesRisk, le_iInf_iff]
  intro κ hκ
  rw [avgRisk_const_left' hl]
  refine le_trans ?_ (iInf_mul_le_lintegral (fun y ↦ ∫⁻ θ, ℓ θ y ∂π))
  simp only [Measure.comp_apply_univ]
  rw [ENNReal.iInf_mul' hl_pos (fun hμ ↦ h_zero (by simpa using hμ))]
  gcongr with y
  rw [lintegral_mul_const]
  fun_prop

lemma bayesRisk_const_of_neZero (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [NeZero μ] [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y * μ .univ ∂π :=
  bayesRisk_const' hl μ π (by simp) (by simp [NeZero.out])

lemma bayesRisk_const_of_nonempty [Nonempty 𝓨] (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [IsFiniteMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y * μ .univ ∂π :=
  bayesRisk_const' hl μ π (by simp) (fun _ ↦ inferInstance)

lemma bayesRisk_const (hl : Measurable (uncurry ℓ))
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.const Θ μ) π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂π := by
  simp [bayesRisk_const_of_neZero hl μ π]

end Const

lemma avgRisk_le_mul' (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsFiniteKernel κ]
    (π : Measure Θ) {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    avgRisk ℓ P κ π ≤ C * IsFiniteKernel.bound κ * IsFiniteKernel.bound P * π Set.univ := by
  rw [avgRisk]
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
lemma avgRisk_le_mul (P : Kernel Θ 𝓧) [IsFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ]
    (π : Measure Θ) {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    avgRisk ℓ P κ π ≤ C * IsFiniteKernel.bound P * π Set.univ := by
  rw [avgRisk]
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

lemma bayesRisk_le_mul [h𝓨 : Nonempty 𝓨] (P : Kernel Θ 𝓧)
    [IsFiniteKernel P] (π : Measure Θ) {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesRisk ℓ P π ≤ C * (IsFiniteKernel.bound P) * π Set.univ := by
  refine iInf₂_le_of_le (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) inferInstance ?_
  exact avgRisk_le_mul P (Kernel.const 𝓧 (Measure.dirac h𝓨.some)) π hℓC

/-- For a bounded loss, the Bayes risk with respect to a prior is finite. -/
lemma bayesRisk_lt_top [h𝓨 : Nonempty 𝓨] (P : Kernel Θ 𝓧)
    [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] {C : ℝ≥0} (hℓC : ∀ θ y, ℓ θ y ≤ C) :
    bayesRisk ℓ P π < ∞ := by
  refine (bayesRisk_le_mul P π hℓC).trans_lt ?_
  simp [ENNReal.mul_lt_top_iff, IsFiniteKernel.bound_lt_top P]

section Subsingleton

lemma bayesRisk_discard (hl : Measurable (uncurry ℓ)) (π : Measure Θ) [SFinite π] :
    bayesRisk ℓ (Kernel.discard Θ) π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂π := by
  rw [Kernel.discard_eq_const, bayesRisk_const hl]

lemma bayesRisk_eq_iInf_measure_of_subsingleton [Subsingleton 𝓧] [Nonempty 𝓨] :
    bayesRisk ℓ P π
      = ⨅ (μ : Measure 𝓨) (_ : IsProbabilityMeasure μ), avgRisk ℓ P (Kernel.const 𝓧 μ) π := by
  rcases isEmpty_or_nonempty 𝓧 with hX | hX
  · simp [iInf_subtype']
  obtain x := Nonempty.some hX
  rw [bayesRisk, iInf_subtype', iInf_subtype']
  let e : {κ : Kernel 𝓧 𝓨 // IsMarkovKernel κ} ≃ {μ : Measure 𝓨 // IsProbabilityMeasure μ} :=
    { toFun κ := ⟨κ.1 x, by have := κ.2.isProbabilityMeasure x; infer_instance⟩
      invFun μ := ⟨Kernel.const 𝓧 μ, by have := μ.2; infer_instance⟩
      left_inv κ := by ext y; simp only [Kernel.const_apply, Subsingleton.elim x y]
      right_inv μ := by simp }
  rw [← Equiv.iInf_comp e.symm]
  congr

lemma bayesRisk_of_subsingleton' [Subsingleton 𝓧] [Nonempty 𝓨] [SFinite π]
    (hl : Measurable (uncurry ℓ)) :
    bayesRisk ℓ P π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y * P θ .univ ∂π := by
  refine le_antisymm (bayesRisk_le_iInf' hl _ _) ?_
  rw [bayesRisk_eq_iInf_measure_of_subsingleton]
  simp only [avgRisk_const_right, le_iInf_iff]
  refine fun μ hμ ↦ (iInf_le_lintegral (μ := μ) _).trans_eq ?_
  rw [lintegral_lintegral_swap]
  · congr with θ
    rw [lintegral_mul_const _ (by fun_prop), mul_comm]
  · have := P.measurable_coe .univ
    fun_prop

lemma bayesRisk_of_subsingleton [Subsingleton 𝓧] [Nonempty 𝓨] [IsMarkovKernel P] [SFinite π]
    (hl : Measurable (uncurry ℓ)) :
    bayesRisk ℓ P π = ⨅ y : 𝓨, ∫⁻ θ, ℓ θ y ∂π := by
  simp [bayesRisk_of_subsingleton' hl]

lemma bayesRisk_eq_bayesRisk_discard_of_subsingleton [Subsingleton 𝓧] [Nonempty 𝓨]
    [IsMarkovKernel P] [SFinite π] (hl : Measurable (uncurry ℓ)) :
    bayesRisk ℓ P π = bayesRisk ℓ (Kernel.discard Θ) π := by
  simp [bayesRisk_of_subsingleton hl]

end Subsingleton

lemma avgRisk_withDensity (hl : Measurable (uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsSFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ]
    (π : Measure Θ) {f : Θ → ℝ≥0∞} (hf : Measurable f) :
    avgRisk ℓ (P.withDensity (fun θ _ ↦ f θ)) κ π = avgRisk ℓ P κ (π.withDensity f) := by
  simp only [avgRisk]
  rw [lintegral_withDensity_eq_lintegral_mul _ hf (by fun_prop)]
  congr with θ
  rw [Kernel.comp_apply, Kernel.withDensity_apply _ (by fun_prop), Pi.mul_apply, Kernel.comp_apply]
  simp

lemma bayesRisk_withDensity (hl : Measurable (uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsSFiniteKernel P] (π : Measure Θ)
    {f : Θ → ℝ≥0∞} (hf : Measurable f) :
    bayesRisk ℓ (P.withDensity (fun θ _ ↦ f θ)) π = bayesRisk ℓ P (π.withDensity f) := by
  simp_rw [bayesRisk]
  congr! 3 with κ hκ
  rw [avgRisk_withDensity hl P κ π hf]

section Compositions

/-- **Data processing inequality** for the Bayes risk with respect to a prior: composition of the
data generating kernel by a Markov kernel increases the risk. -/
lemma bayesRisk_le_bayesRisk_comp (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    (π : Measure Θ) (η : Kernel 𝓧 𝓧') [IsMarkovKernel η] :
    bayesRisk ℓ P π ≤ bayesRisk ℓ (η ∘ₖ P) π := by
  simp only [bayesRisk, avgRisk, le_iInf_iff]
  intro κ hκ
  rw [← κ.comp_assoc η]
  exact iInf_le_of_le (κ ∘ₖ η) (iInf_le_of_le inferInstance le_rfl)

lemma bayesRisk_compProd_le_bayesRisk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (π : Measure Θ) (η : Kernel (Θ × 𝓧) 𝓧') [IsMarkovKernel η] :
    bayesRisk ℓ (P ⊗ₖ η) π ≤ bayesRisk ℓ P π := by
  have : P = (Kernel.deterministic Prod.fst (by fun_prop)) ∘ₖ (P ⊗ₖ η) := by
    rw [Kernel.deterministic_comp_eq_map, ← Kernel.fst_eq, Kernel.fst_compProd]
  conv_rhs => rw [this]
  exact bayesRisk_le_bayesRisk_comp _ _ _ _

lemma avgRisk_comap_measurableEquiv (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (κ : Kernel 𝓧 𝓨) [IsSFiniteKernel κ] (π : Measure Θ) (e : Θ' ≃ᵐ Θ) :
    avgRisk (fun θ ↦ ℓ (e θ)) (P.comap e e.measurable) κ (π.comap e)
      = avgRisk ℓ P κ π := by
  simp only [avgRisk]
  rw [← MeasurableEquiv.map_symm, lintegral_map (by fun_prop) e.symm.measurable]
  congr with θ
  congr
  · ext s hs
    simp [κ.comp_apply' _ _ hs, Kernel.comap_apply]
  · simp

lemma bayesRisk_comap_measurableEquiv (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧)
    [IsSFiniteKernel P] (π : Measure Θ) (e : Θ' ≃ᵐ Θ) :
    bayesRisk (fun θ ↦ ℓ (e θ)) (P.comap e e.measurable) (π.comap e)
      = bayesRisk ℓ P π := by
  simp only [bayesRisk, avgRisk_comap_measurableEquiv hl P _ π e]

end Compositions

end ProbabilityTheory
