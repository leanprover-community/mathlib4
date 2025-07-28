/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Decision.Binary

/-!
# Statistical information

TODO: cite DeGroot and also Duchi et al.

## Main definitions

* `statInfo`

## Main statements

* `statInfo_comp_le`: data-processing inequality

## Notation

## Implementation details

-/

open MeasureTheory Set Function

open scoped ENNReal NNReal

namespace ProbabilityTheory

@[simp]
lemma Kernel.comp_discard' {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (κ : Kernel α β) : discard β ∘ₖ κ = (discard α).withDensity (fun a _ ↦ κ a .univ) := by
  ext a s hs
  simp only [comp_apply' _ _ _ hs, discard_apply, MeasurableSpace.measurableSet_top,
    Measure.dirac_apply', MeasureTheory.lintegral_const]
  rw [Kernel.withDensity_apply']
  · simp [mul_comm]
  · have : Measurable (fun a ↦ κ a .univ) := κ.measurable_coe .univ
    fun_prop

instance {α : Type*} [MeasurableSpace α] [Countable α] [DiscreteMeasurableSpace α]
    {μ : Measure α} : SFinite μ := by
  have : μ = Measure.sum (fun a ↦ μ {a} • Measure.dirac a) := by
    ext s hs
    simp only [Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply]
    rw [← biUnion_of_singleton s, measure_biUnion]
    · rw [tsum_subtype s (fun a ↦ μ {a})]
      congr with a
      classical
      simp [indicator_apply]
    · exact to_countable s
    · intro i j hij
      simp
    · exact fun _ _ ↦ measurableSet_singleton _
  rw [this]
  infer_instance

variable {Θ 𝓧 𝓨 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧} [MeasurableSpace 𝓨]
  {π : Measure Θ} {P : Kernel Θ 𝓧} {ℓ : Θ → 𝓨 → ℝ≥0∞}

noncomputable
def riskIncrease (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (π : Measure Θ) : ℝ≥0∞ :=
  bayesRiskPrior ℓ (Kernel.discard 𝓧 ∘ₖ P) π - bayesRiskPrior ℓ P π

lemma riskIncrease_eq_iInf_sub' (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧)
    (π : Measure Θ) [SFinite π] :
    riskIncrease ℓ P π = (⨅ z : 𝓨, ∫⁻ θ, P θ univ * ℓ θ z ∂π) - bayesRiskPrior ℓ P π := by
  simp_rw [riskIncrease, Kernel.comp_discard']
  congr
  -- extract lemma
  simp [bayesRiskPrior, bayesianRisk, risk]
  sorry

lemma riskIncrease_eq_iInf_sub (hl : Measurable (uncurry ℓ)) (P : Kernel Θ 𝓧) [IsMarkovKernel P]
    (π : Measure Θ) [SFinite π] :
    riskIncrease ℓ P π = (⨅ z : 𝓨, ∫⁻ θ, ℓ θ z ∂π) - bayesRiskPrior ℓ P π := by
  simp_rw [riskIncrease, Kernel.comp_discard, bayesRiskPrior_discard hl]

@[simp] lemma riskIncrease_zero_left_of_isEmpty_of_isEmpty [IsEmpty 𝓧] [IsEmpty 𝓨] :
    riskIncrease ℓ (0 : Kernel Θ 𝓧) π = ∞ := by
  simp [riskIncrease]

@[simp] lemma riskIncrease_zero_left_of_nonempty_of_isEmpty [Nonempty 𝓧] [IsEmpty 𝓨] :
    riskIncrease ℓ (0 : Kernel Θ 𝓧) π = 0 := by
  simp [riskIncrease]

@[simp] lemma riskIncrease_zero_left [Nonempty 𝓨] : riskIncrease ℓ (0 : Kernel Θ 𝓧) π = 0 := by
  simp [riskIncrease]

@[simp] lemma riskIncrease_zero_right [Nonempty 𝓨] : riskIncrease ℓ P (0 : Measure Θ) = 0 := by
  simp [riskIncrease]

@[simp] lemma riskIncrease_const (hl : Measurable (uncurry ℓ))
    [SFinite π] {μ : Measure 𝓧} [IsProbabilityMeasure μ] :
    riskIncrease ℓ (Kernel.const Θ μ) π = 0 := by
  simp [riskIncrease, bayesRiskPrior_const hl]

lemma riskIncrease_le_iInf' (hl : Measurable (uncurry ℓ)) [SFinite π] :
    riskIncrease ℓ P π ≤ ⨅ z : 𝓨, ∫⁻ θ, P θ univ * ℓ θ z ∂π :=
  riskIncrease_eq_iInf_sub' hl P π ▸ tsub_le_self

lemma riskIncrease_le_iInf (hl : Measurable (uncurry ℓ)) [IsMarkovKernel P] [SFinite π] :
    riskIncrease ℓ P π ≤ ⨅ z : 𝓨, ∫⁻ θ, ℓ θ z ∂π :=
  riskIncrease_eq_iInf_sub hl P π ▸ tsub_le_self

lemma riskIncrease_lt_top' (hl : Measurable (uncurry ℓ)) [IsFiniteKernel P] [IsFiniteMeasure π]
    {y : 𝓨} (h_finite : ∫⁻ θ, P θ univ * ℓ θ y ∂π ≠ ⊤) :
    riskIncrease ℓ P π < ⊤ :=
  (riskIncrease_le_iInf' hl).trans_lt (iInf_lt_top.mpr ⟨y, h_finite.lt_top⟩)

lemma riskIncrease_lt_top (hl : Measurable (uncurry ℓ)) [IsMarkovKernel P] [IsFiniteMeasure π]
    {y : 𝓨} (h_finite : ∫⁻ θ, ℓ θ y ∂π ≠ ⊤) :
    riskIncrease ℓ P π < ⊤ :=
  (riskIncrease_le_iInf hl).trans_lt (iInf_lt_top.mpr ⟨y, h_finite.lt_top⟩)

/-- **Data processing inequality** for the risk increase. -/
lemma riskIncrease_comp_le (P : Kernel Θ 𝓧) (π : Measure Θ) (η : Kernel 𝓧 𝓨) [IsMarkovKernel η] :
    riskIncrease ℓ (η ∘ₖ P) π ≤ riskIncrease ℓ P π := by
  refine tsub_le_tsub ?_ (bayesRiskPrior_le_bayesRiskPrior_comp _ _ _ _)
  rw [← Kernel.comp_assoc]
  simp

end ProbabilityTheory
