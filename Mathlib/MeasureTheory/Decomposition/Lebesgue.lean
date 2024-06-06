/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Decomposition.SignedHahn
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

#align_import measure_theory.decomposition.lebesgue from "leanprover-community/mathlib"@"b2ff9a3d7a15fd5b0f060b135421d6a89a999c2f"

/-!
# Lebesgue decomposition

This file proves the Lebesgue decomposition theorem. The Lebesgue decomposition theorem states that,
given two σ-finite measures `μ` and `ν`, there exists a σ-finite measure `ξ` and a measurable
function `f` such that `μ = ξ + fν` and `ξ` is mutually singular with respect to `ν`.

The Lebesgue decomposition provides the Radon-Nikodym theorem readily.

## Main definitions

* `MeasureTheory.Measure.HaveLebesgueDecomposition` : A pair of measures `μ` and `ν` is said
  to `HaveLebesgueDecomposition` if there exist a measure `ξ` and a measurable function `f`,
  such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.withDensity f`
* `MeasureTheory.Measure.singularPart` : If a pair of measures `HaveLebesgueDecomposition`,
  then `singularPart` chooses the measure from `HaveLebesgueDecomposition`, otherwise it
  returns the zero measure.
* `MeasureTheory.Measure.rnDeriv`: If a pair of measures
  `HaveLebesgueDecomposition`, then `rnDeriv` chooses the measurable function from
  `HaveLebesgueDecomposition`, otherwise it returns the zero function.

## Main results

* `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite` :
  the Lebesgue decomposition theorem.
* `MeasureTheory.Measure.eq_singularPart` : Given measures `μ` and `ν`, if `s` is a measure
  mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`, then
  `s = μ.singularPart ν`.
* `MeasureTheory.Measure.eq_rnDeriv` : Given measures `μ` and `ν`, if `s` is a
  measure mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`,
  then `f = μ.rnDeriv ν`.

## Tags

Lebesgue decomposition theorem
-/

open scoped MeasureTheory NNReal ENNReal

open Set

namespace MeasureTheory

namespace Measure

variable {α β : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

/-- A pair of measures `μ` and `ν` is said to `HaveLebesgueDecomposition` if there exists a
measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular with respect to
`ν` and `μ = ξ + ν.withDensity f`. -/
class HaveLebesgueDecomposition (μ ν : Measure α) : Prop where
  lebesgue_decomposition :
    ∃ p : Measure α × (α → ℝ≥0∞), Measurable p.2 ∧ p.1 ⟂ₘ ν ∧ μ = p.1 + ν.withDensity p.2
#align measure_theory.measure.have_lebesgue_decomposition MeasureTheory.Measure.HaveLebesgueDecomposition
#align measure_theory.measure.have_lebesgue_decomposition.lebesgue_decomposition MeasureTheory.Measure.HaveLebesgueDecomposition.lebesgue_decomposition

open Classical in
/-- If a pair of measures `HaveLebesgueDecomposition`, then `singularPart` chooses the
measure from `HaveLebesgueDecomposition`, otherwise it returns the zero measure. For sigma-finite
measures, `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`. -/
noncomputable irreducible_def singularPart (μ ν : Measure α) : Measure α :=
  if h : HaveLebesgueDecomposition μ ν then (Classical.choose h.lebesgue_decomposition).1 else 0
#align measure_theory.measure.singular_part MeasureTheory.Measure.singularPart

open Classical in
/-- If a pair of measures `HaveLebesgueDecomposition`, then `rnDeriv` chooses the
measurable function from `HaveLebesgueDecomposition`, otherwise it returns the zero function.
For sigma-finite measures, `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`. -/
noncomputable irreducible_def rnDeriv (μ ν : Measure α) : α → ℝ≥0∞ :=
  if h : HaveLebesgueDecomposition μ ν then (Classical.choose h.lebesgue_decomposition).2 else 0
#align measure_theory.measure.rn_deriv MeasureTheory.Measure.rnDeriv

section ByDefinition

theorem haveLebesgueDecomposition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] :
    Measurable (μ.rnDeriv ν) ∧
      μ.singularPart ν ⟂ₘ ν ∧ μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) := by
  rw [singularPart, rnDeriv, dif_pos h, dif_pos h]
  exact Classical.choose_spec h.lebesgue_decomposition
#align measure_theory.measure.have_lebesgue_decomposition_spec MeasureTheory.Measure.haveLebesgueDecomposition_spec

lemma rnDeriv_of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν) :
    μ.rnDeriv ν = 0 := by
  rw [rnDeriv, dif_neg h]

lemma singularPart_of_not_haveLebesgueDecomposition (h : ¬ HaveLebesgueDecomposition μ ν) :
    μ.singularPart ν = 0 := by
  rw [singularPart, dif_neg h]

@[measurability]
theorem measurable_rnDeriv (μ ν : Measure α) : Measurable <| μ.rnDeriv ν := by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).1
  · rw [rnDeriv_of_not_haveLebesgueDecomposition h]
    exact measurable_zero
#align measure_theory.measure.measurable_rn_deriv MeasureTheory.Measure.measurable_rnDeriv

theorem mutuallySingular_singularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν := by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).2.1
  · rw [singularPart_of_not_haveLebesgueDecomposition h]
    exact MutuallySingular.zero_left
#align measure_theory.measure.mutually_singular_singular_part MeasureTheory.Measure.mutuallySingular_singularPart

theorem haveLebesgueDecomposition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) :=
  (haveLebesgueDecomposition_spec μ ν).2.2
#align measure_theory.measure.have_lebesgue_decomposition_add MeasureTheory.Measure.haveLebesgueDecomposition_add

lemma singularPart_add_rnDeriv (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) = μ := (haveLebesgueDecomposition_add μ ν).symm

lemma rnDeriv_add_singularPart (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    ν.withDensity (μ.rnDeriv ν) + μ.singularPart ν = μ := by rw [add_comm, singularPart_add_rnDeriv]

end ByDefinition

section HaveLebesgueDecomposition

instance instHaveLebesgueDecompositionZeroLeft : HaveLebesgueDecomposition 0 ν where
  lebesgue_decomposition := ⟨⟨0, 0⟩, measurable_zero, MutuallySingular.zero_left, by simp⟩

instance instHaveLebesgueDecompositionZeroRight : HaveLebesgueDecomposition μ 0 where
  lebesgue_decomposition := ⟨⟨μ, 0⟩, measurable_zero, MutuallySingular.zero_right, by simp⟩

instance instHaveLebesgueDecompositionSelf : HaveLebesgueDecomposition μ μ where
  lebesgue_decomposition := ⟨⟨0, 1⟩, measurable_const, MutuallySingular.zero_left, by simp⟩

instance haveLebesgueDecompositionSMul' (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : ℝ≥0∞) : (r • μ).HaveLebesgueDecomposition ν where
  lebesgue_decomposition := by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    refine ⟨⟨r • μ.singularPart ν, r • μ.rnDeriv ν⟩, hmeas.const_smul _, hsing.smul _, ?_⟩
    simp only [ENNReal.smul_def]
    rw [withDensity_smul _ hmeas, ← smul_add, ← hadd]

instance haveLebesgueDecompositionSMul (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : ℝ≥0) : (r • μ).HaveLebesgueDecomposition ν := by
  rw [ENNReal.smul_def]; infer_instance
#align measure_theory.measure.have_lebesgue_decomposition_smul MeasureTheory.Measure.haveLebesgueDecompositionSMul

instance haveLebesgueDecompositionSMulRight (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : ℝ≥0) :
    μ.HaveLebesgueDecomposition (r • ν) where
  lebesgue_decomposition := by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    by_cases hr : r = 0
    · exact ⟨⟨μ, 0⟩, measurable_const, by simp [hr], by simp⟩
    refine ⟨⟨μ.singularPart ν, r⁻¹ • μ.rnDeriv ν⟩, hmeas.const_smul _,
      hsing.mono_ac AbsolutelyContinuous.rfl smul_absolutelyContinuous, ?_⟩
    have : r⁻¹ • rnDeriv μ ν = ((r⁻¹ : ℝ≥0) : ℝ≥0∞) • rnDeriv μ ν := by simp [ENNReal.smul_def]
    rw [this, withDensity_smul _ hmeas, ENNReal.smul_def r, withDensity_smul_measure,
      ← smul_assoc, smul_eq_mul, ENNReal.coe_inv hr, ENNReal.inv_mul_cancel, one_smul]
    · exact hadd
    · simp [hr]
    · exact ENNReal.coe_ne_top

theorem haveLebesgueDecomposition_withDensity (μ : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).HaveLebesgueDecomposition μ := ⟨⟨⟨0, f⟩, hf, .zero_left, (zero_add _).symm⟩⟩

instance haveLebesgueDecompositionRnDeriv (μ ν : Measure α) :
    HaveLebesgueDecomposition (ν.withDensity (μ.rnDeriv ν)) ν :=
  haveLebesgueDecomposition_withDensity ν (measurable_rnDeriv _ _)

instance instHaveLebesgueDecompositionSingularPart :
    HaveLebesgueDecomposition (μ.singularPart ν) ν :=
  ⟨⟨μ.singularPart ν, 0⟩, measurable_zero, mutuallySingular_singularPart μ ν, by simp⟩

end HaveLebesgueDecomposition

theorem singularPart_le (μ ν : Measure α) : μ.singularPart ν ≤ μ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
    exact Measure.le_add_right le_rfl
  · rw [singularPart, dif_neg hl]
    exact Measure.zero_le μ
#align measure_theory.measure.singular_part_le MeasureTheory.Measure.singularPart_le

theorem withDensity_rnDeriv_le (μ ν : Measure α) : ν.withDensity (μ.rnDeriv ν) ≤ μ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
    exact Measure.le_add_left le_rfl
  · rw [rnDeriv, dif_neg hl, withDensity_zero]
    exact Measure.zero_le μ
#align measure_theory.measure.with_density_rn_deriv_le MeasureTheory.Measure.withDensity_rnDeriv_le

lemma _root_.AEMeasurable.singularPart {β : Type*} {_ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (ν : Measure α) :
    AEMeasurable f (μ.singularPart ν) :=
  AEMeasurable.mono_measure hf (Measure.singularPart_le _ _)

lemma _root_.AEMeasurable.withDensity_rnDeriv {β : Type*} {_ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (ν : Measure α) :
    AEMeasurable f (ν.withDensity (μ.rnDeriv ν)) :=
  AEMeasurable.mono_measure hf (Measure.withDensity_rnDeriv_le _ _)

lemma MutuallySingular.singularPart (h : μ ⟂ₘ ν) (ν' : Measure α) :
    μ.singularPart ν' ⟂ₘ ν :=
  h.mono (singularPart_le μ ν') le_rfl

lemma absolutelyContinuous_withDensity_rnDeriv [HaveLebesgueDecomposition ν μ] (hμν : μ ≪ ν) :
    μ ≪ μ.withDensity (ν.rnDeriv μ) := by
  rw [haveLebesgueDecomposition_add ν μ] at hμν
  refine AbsolutelyContinuous.mk (fun s _ hνs ↦ ?_)
  obtain ⟨t, _, ht1, ht2⟩ := mutuallySingular_singularPart ν μ
  rw [← inter_union_compl s]
  refine le_antisymm ((measure_union_le (s ∩ t) (s ∩ tᶜ)).trans ?_) (zero_le _)
  simp only [nonpos_iff_eq_zero, add_eq_zero]
  constructor
  · refine hμν ?_
    simp only [coe_add, Pi.add_apply, add_eq_zero]
    constructor
    · exact measure_mono_null Set.inter_subset_right ht1
    · exact measure_mono_null Set.inter_subset_left hνs
  · exact measure_mono_null Set.inter_subset_right ht2

lemma singularPart_eq_zero_of_ac (h : μ ≪ ν) : μ.singularPart ν = 0 := by
  rw [← MutuallySingular.self_iff]
  exact MutuallySingular.mono_ac (mutuallySingular_singularPart _ _)
    AbsolutelyContinuous.rfl ((absolutelyContinuous_of_le (singularPart_le _ _)).trans h)

@[simp]
theorem singularPart_zero (ν : Measure α) : (0 : Measure α).singularPart ν = 0 :=
  singularPart_eq_zero_of_ac (AbsolutelyContinuous.zero _)
#align measure_theory.measure.singular_part_zero MeasureTheory.Measure.singularPart_zero

@[simp]
lemma singularPart_zero_right (μ : Measure α) : μ.singularPart 0 = μ := by
  conv_rhs => rw [haveLebesgueDecomposition_add μ 0]
  simp

lemma singularPart_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    μ.singularPart ν = 0 ↔ μ ≪ ν := by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h ↦ ?_, singularPart_eq_zero_of_ac⟩
  rw [h, zero_add] at h_dec
  rw [h_dec]
  exact withDensity_absolutelyContinuous ν _

@[simp]
lemma withDensity_rnDeriv_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    ν.withDensity (μ.rnDeriv ν) = 0 ↔ μ ⟂ₘ ν := by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [h, add_zero] at h_dec
    rw [h_dec]
    exact mutuallySingular_singularPart μ ν
  · rw [← MutuallySingular.self_iff]
    rw [h_dec, MutuallySingular.add_left_iff] at h
    refine MutuallySingular.mono_ac h.2 AbsolutelyContinuous.rfl ?_
    exact withDensity_absolutelyContinuous _ _

@[simp]
lemma rnDeriv_eq_zero (μ ν : Measure α) [μ.HaveLebesgueDecomposition ν] :
    μ.rnDeriv ν =ᵐ[ν] 0 ↔ μ ⟂ₘ ν := by
  rw [← withDensity_rnDeriv_eq_zero, withDensity_eq_zero_iff (measurable_rnDeriv _ _).aemeasurable]

lemma rnDeriv_zero (ν : Measure α) : (0 : Measure α).rnDeriv ν =ᵐ[ν] 0 := by
  rw [rnDeriv_eq_zero]
  exact MutuallySingular.zero_left

lemma MutuallySingular.rnDeriv_ae_eq_zero (hμν : μ ⟂ₘ ν) :
    μ.rnDeriv ν =ᵐ[ν] 0 := by
  by_cases h : μ.HaveLebesgueDecomposition ν
  · rw [rnDeriv_eq_zero]
    exact hμν
  · rw [rnDeriv_of_not_haveLebesgueDecomposition h]

@[simp]
theorem singularPart_withDensity (ν : Measure α) (f : α → ℝ≥0∞) :
    (ν.withDensity f).singularPart ν = 0 :=
  singularPart_eq_zero_of_ac (withDensity_absolutelyContinuous _ _)
#align measure_theory.measure.singular_part_with_density MeasureTheory.Measure.singularPart_withDensity

lemma rnDeriv_singularPart (μ ν : Measure α) :
    (μ.singularPart ν).rnDeriv ν =ᵐ[ν] 0 := by
  rw [rnDeriv_eq_zero]
  exact mutuallySingular_singularPart μ ν

@[simp]
lemma singularPart_self (μ : Measure α) : μ.singularPart μ = 0 :=
  singularPart_eq_zero_of_ac Measure.AbsolutelyContinuous.rfl

lemma rnDeriv_self (μ : Measure α) [SigmaFinite μ] : μ.rnDeriv μ =ᵐ[μ] fun _ ↦ 1 := by
  have h := rnDeriv_add_singularPart μ μ
  rw [singularPart_self, add_zero] at h
  have h_one : μ = μ.withDensity 1 := by simp
  conv_rhs at h => rw [h_one]
  rwa [withDensity_eq_iff_of_sigmaFinite (measurable_rnDeriv _ _).aemeasurable] at h
  exact aemeasurable_const

lemma singularPart_eq_self [μ.HaveLebesgueDecomposition ν] : μ.singularPart ν = μ ↔ μ ⟂ₘ ν := by
  have h_dec := haveLebesgueDecomposition_add μ ν
  refine ⟨fun h ↦ ?_, fun  h ↦ ?_⟩
  · rw [← h]
    exact mutuallySingular_singularPart _ _
  · conv_rhs => rw [h_dec]
    rw [(withDensity_rnDeriv_eq_zero _ _).mpr h, add_zero]

@[simp]
lemma singularPart_singularPart (μ ν : Measure α) :
    (μ.singularPart ν).singularPart ν = μ.singularPart ν := by
  rw [Measure.singularPart_eq_self]
  exact Measure.mutuallySingular_singularPart _ _

instance singularPart.instIsFiniteMeasure [IsFiniteMeasure μ] :
    IsFiniteMeasure (μ.singularPart ν) :=
  isFiniteMeasure_of_le μ <| singularPart_le μ ν
#align measure_theory.measure.singular_part.measure_theory.is_finite_measure MeasureTheory.Measure.singularPart.instIsFiniteMeasure

instance singularPart.instSigmaFinite [SigmaFinite μ] : SigmaFinite (μ.singularPart ν) :=
  sigmaFinite_of_le μ <| singularPart_le μ ν
#align measure_theory.measure.singular_part.measure_theory.sigma_finite MeasureTheory.Measure.singularPart.instSigmaFinite

instance singularPart.instIsLocallyFiniteMeasure [TopologicalSpace α] [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.singularPart ν) :=
  isLocallyFiniteMeasure_of_le <| singularPart_le μ ν
#align measure_theory.measure.singular_part.measure_theory.is_locally_finite_measure MeasureTheory.Measure.singularPart.instIsLocallyFiniteMeasure

instance withDensity.instIsFiniteMeasure [IsFiniteMeasure μ] :
    IsFiniteMeasure (ν.withDensity <| μ.rnDeriv ν) :=
  isFiniteMeasure_of_le μ <| withDensity_rnDeriv_le μ ν
#align measure_theory.measure.with_density.measure_theory.is_finite_measure MeasureTheory.Measure.withDensity.instIsFiniteMeasure

instance withDensity.instSigmaFinite [SigmaFinite μ] :
    SigmaFinite (ν.withDensity <| μ.rnDeriv ν) :=
  sigmaFinite_of_le μ <| withDensity_rnDeriv_le μ ν
#align measure_theory.measure.with_density.measure_theory.sigma_finite MeasureTheory.Measure.withDensity.instSigmaFinite

instance withDensity.instIsLocallyFiniteMeasure [TopologicalSpace α] [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (ν.withDensity <| μ.rnDeriv ν) :=
  isLocallyFiniteMeasure_of_le <| withDensity_rnDeriv_le μ ν
#align measure_theory.measure.with_density.measure_theory.is_locally_finite_measure MeasureTheory.Measure.withDensity.instIsLocallyFiniteMeasure

section RNDerivFinite

theorem lintegral_rnDeriv_lt_top_of_measure_ne_top (ν : Measure α) {s : Set α} (hs : μ s ≠ ∞) :
    ∫⁻ x in s, μ.rnDeriv ν x ∂ν < ∞ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · suffices (∫⁻ x in toMeasurable μ s, μ.rnDeriv ν x ∂ν) < ∞ from
      lt_of_le_of_lt (lintegral_mono_set (subset_toMeasurable _ _)) this
    rw [← withDensity_apply _ (measurableSet_toMeasurable _ _)]
    calc
      _ ≤ (singularPart μ ν) (toMeasurable μ s) + _ := le_add_self
      _ = μ s := by rw [← Measure.add_apply, ← haveLebesgueDecomposition_add, measure_toMeasurable]
      _ < ⊤ := hs.lt_top
  · simp only [Measure.rnDeriv, dif_neg hl, Pi.zero_apply, lintegral_zero, ENNReal.zero_lt_top]
#align measure_theory.measure.lintegral_rn_deriv_lt_top_of_measure_ne_top MeasureTheory.Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top

theorem lintegral_rnDeriv_lt_top (μ ν : Measure α) [IsFiniteMeasure μ] :
    ∫⁻ x, μ.rnDeriv ν x ∂ν < ∞ := by
  rw [← set_lintegral_univ]
  exact lintegral_rnDeriv_lt_top_of_measure_ne_top _ (measure_lt_top _ _).ne
#align measure_theory.measure.lintegral_rn_deriv_lt_top MeasureTheory.Measure.lintegral_rnDeriv_lt_top

lemma integrable_toReal_rnDeriv [IsFiniteMeasure μ] :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top _ _).ne

/-- The Radon-Nikodym derivative of a sigma-finite measure `μ` with respect to another
measure `ν` is `ν`-almost everywhere finite. -/
theorem rnDeriv_lt_top (μ ν : Measure α) [SigmaFinite μ] : ∀ᵐ x ∂ν, μ.rnDeriv ν x < ∞ := by
  suffices ∀ n, ∀ᵐ x ∂ν, x ∈ spanningSets μ n → μ.rnDeriv ν x < ∞ by
    filter_upwards [ae_all_iff.2 this] with _ hx using hx _ (mem_spanningSetsIndex _ _)
  intro n
  rw [← ae_restrict_iff' (measurable_spanningSets _ _)]
  apply ae_lt_top (measurable_rnDeriv _ _)
  refine (lintegral_rnDeriv_lt_top_of_measure_ne_top _ ?_).ne
  exact (measure_spanningSets_lt_top _ _).ne
#align measure_theory.measure.rn_deriv_lt_top MeasureTheory.Measure.rnDeriv_lt_top

lemma rnDeriv_ne_top (μ ν : Measure α) [SigmaFinite μ] : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ ∞ := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx using hx.ne

end RNDerivFinite

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `s = μ.singularPart μ`.

This theorem provides the uniqueness of the `singularPart` in the Lebesgue decomposition theorem,
while `MeasureTheory.Measure.eq_rnDeriv` provides the uniqueness of the
`rnDeriv`. -/
theorem eq_singularPart {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : s = μ.singularPart ν := by
  have : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S ∩ T)ᶜ = 0 := by
    rw [compl_inter]
    refine nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) ?_)
    rw [hT₃, hS₃, add_zero]
  have heq : s.restrict (S ∩ T)ᶜ = (μ.singularPart ν).restrict (S ∩ T)ᶜ := by
    ext1 A hA
    have hf : ν.withDensity f (A ∩ (S ∩ T)ᶜ) = 0 := by
      refine withDensity_absolutelyContinuous ν _ ?_
      rw [← nonpos_iff_eq_zero]
      exact hνinter ▸ measure_mono inter_subset_right
    have hrn : ν.withDensity (μ.rnDeriv ν) (A ∩ (S ∩ T)ᶜ) = 0 := by
      refine withDensity_absolutelyContinuous ν _ ?_
      rw [← nonpos_iff_eq_zero]
      exact hνinter ▸ measure_mono inter_subset_right
    rw [restrict_apply hA, restrict_apply hA, ← add_zero (s (A ∩ (S ∩ T)ᶜ)), ← hf, ← add_apply, ←
      hadd, add_apply, hrn, add_zero]
  have heq' : ∀ A : Set α, MeasurableSet A → s A = s.restrict (S ∩ T)ᶜ A := by
    intro A hA
    have hsinter : s (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hS₂ ▸ measure_mono (inter_subset_right.trans inter_subset_left)
    rw [restrict_apply hA, ← diff_eq, AEDisjoint.measure_diff_left hsinter]
  ext1 A hA
  have hμinter : μ.singularPart ν (A ∩ (S ∩ T)) = 0 := by
    rw [← nonpos_iff_eq_zero]
    exact hT₂ ▸ measure_mono (inter_subset_right.trans inter_subset_right)
  rw [heq' A hA, heq, restrict_apply hA, ← diff_eq, AEDisjoint.measure_diff_left hμinter]
#align measure_theory.measure.eq_singular_part MeasureTheory.Measure.eq_singularPart

theorem singularPart_smul (μ ν : Measure α) (r : ℝ≥0) :
    (r • μ).singularPart ν = r • μ.singularPart ν := by
  by_cases hr : r = 0
  · rw [hr, zero_smul, zero_smul, singularPart_zero]
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul (r : ℝ≥0∞))
          (MutuallySingular.smul r (mutuallySingular_singularPart _ _)) ?_).symm
    rw [withDensity_smul _ (measurable_rnDeriv _ _), ← smul_add,
      ← haveLebesgueDecomposition_add μ ν, ENNReal.smul_def]
  · rw [singularPart, singularPart, dif_neg hl, dif_neg, smul_zero]
    refine fun hl' ↦ hl ?_
    rw [← inv_smul_smul₀ hr μ]
    infer_instance
#align measure_theory.measure.singular_part_smul MeasureTheory.Measure.singularPart_smul

theorem singularPart_smul_right (μ ν : Measure α) (r : ℝ≥0) (hr : r ≠ 0) :
    μ.singularPart (r • ν) = μ.singularPart ν := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul r⁻¹) ?_ ?_).symm
    · exact (mutuallySingular_singularPart μ ν).mono_ac AbsolutelyContinuous.rfl
        smul_absolutelyContinuous
    · rw [ENNReal.smul_def r, withDensity_smul_measure, ← withDensity_smul]
      swap; · exact (measurable_rnDeriv _ _).const_smul _
      convert haveLebesgueDecomposition_add μ ν
      ext x
      simp only [Pi.smul_apply]
      rw [← ENNReal.smul_def, smul_inv_smul₀ hr]
  · rw [singularPart, singularPart, dif_neg hl, dif_neg]
    refine fun hl' ↦ hl ?_
    rw [← inv_smul_smul₀ hr ν]
    infer_instance

theorem singularPart_add (μ₁ μ₂ ν : Measure α) [HaveLebesgueDecomposition μ₁ ν]
    [HaveLebesgueDecomposition μ₂ ν] :
    (μ₁ + μ₂).singularPart ν = μ₁.singularPart ν + μ₂.singularPart ν := by
  refine (eq_singularPart ((measurable_rnDeriv μ₁ ν).add (measurable_rnDeriv μ₂ ν))
    ((mutuallySingular_singularPart _ _).add_left (mutuallySingular_singularPart _ _)) ?_).symm
  erw [withDensity_add_left (measurable_rnDeriv μ₁ ν)]
  conv_rhs => rw [add_assoc, add_comm (μ₂.singularPart ν), ← add_assoc, ← add_assoc]
  rw [← haveLebesgueDecomposition_add μ₁ ν, add_assoc, add_comm (ν.withDensity (μ₂.rnDeriv ν)),
    ← haveLebesgueDecomposition_add μ₂ ν]
#align measure_theory.measure.singular_part_add MeasureTheory.Measure.singularPart_add

lemma singularPart_restrict (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).singularPart ν = (μ.singularPart ν).restrict s := by
  refine (Measure.eq_singularPart (f := s.indicator (μ.rnDeriv ν)) ?_ ?_ ?_).symm
  · exact (μ.measurable_rnDeriv ν).indicator hs
  · exact (Measure.mutuallySingular_singularPart μ ν).restrict s
  · ext t
    rw [withDensity_indicator hs, ← restrict_withDensity hs, ← Measure.restrict_add,
      ← μ.haveLebesgueDecomposition_add ν]

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `f = μ.rnDeriv ν`.

This theorem provides the uniqueness of the `rnDeriv` in the Lebesgue decomposition
theorem, while `MeasureTheory.Measure.eq_singularPart` provides the uniqueness of the
`singularPart`. Here, the uniqueness is given in terms of the measures, while the uniqueness in
terms of the functions is given in `eq_rnDeriv`. -/
theorem eq_withDensity_rnDeriv {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : ν.withDensity f = ν.withDensity (μ.rnDeriv ν) := by
  have : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S ∩ T)ᶜ = 0 := by
    rw [compl_inter]
    refine nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) ?_)
    rw [hT₃, hS₃, add_zero]
  have heq :
    (ν.withDensity f).restrict (S ∩ T) = (ν.withDensity (μ.rnDeriv ν)).restrict (S ∩ T) := by
    ext1 A hA
    have hs : s (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hS₂ ▸ measure_mono (inter_subset_right.trans inter_subset_left)
    have hsing : μ.singularPart ν (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hT₂ ▸ measure_mono (inter_subset_right.trans inter_subset_right)
    rw [restrict_apply hA, restrict_apply hA, ← add_zero (ν.withDensity f (A ∩ (S ∩ T))), ← hs, ←
      add_apply, add_comm, ← hadd, add_apply, hsing, zero_add]
  have heq' :
    ∀ A : Set α, MeasurableSet A → ν.withDensity f A = (ν.withDensity f).restrict (S ∩ T) A := by
    intro A hA
    have hνfinter : ν.withDensity f (A ∩ (S ∩ T)ᶜ) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact withDensity_absolutelyContinuous ν f hνinter ▸ measure_mono inter_subset_right
    rw [restrict_apply hA, ← add_zero (ν.withDensity f (A ∩ (S ∩ T))), ← hνfinter, ← diff_eq,
      measure_inter_add_diff _ (hS₁.inter hT₁)]
  ext1 A hA
  have hνrn : ν.withDensity (μ.rnDeriv ν) (A ∩ (S ∩ T)ᶜ) = 0 := by
    rw [← nonpos_iff_eq_zero]
    exact
      withDensity_absolutelyContinuous ν (μ.rnDeriv ν) hνinter ▸
        measure_mono inter_subset_right
  rw [heq' A hA, heq, ← add_zero ((ν.withDensity (μ.rnDeriv ν)).restrict (S ∩ T) A), ← hνrn,
    restrict_apply hA, ← diff_eq, measure_inter_add_diff _ (hS₁.inter hT₁)]
#align measure_theory.measure.eq_with_density_rn_deriv MeasureTheory.Measure.eq_withDensity_rnDeriv

theorem eq_withDensity_rnDeriv₀ {s : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) :
    ν.withDensity f = ν.withDensity (μ.rnDeriv ν) := by
  rw [withDensity_congr_ae hf.ae_eq_mk] at hadd ⊢
  exact eq_withDensity_rnDeriv hf.measurable_mk hs hadd

theorem eq_rnDeriv₀ [SigmaFinite ν] {s : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) :
    f =ᵐ[ν] μ.rnDeriv ν :=
  (withDensity_eq_iff_of_sigmaFinite hf (measurable_rnDeriv _ _).aemeasurable).mp
    (eq_withDensity_rnDeriv₀ hf hs hadd)

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `f = μ.rnDeriv ν`.

This theorem provides the uniqueness of the `rnDeriv` in the Lebesgue decomposition
theorem, while `MeasureTheory.Measure.eq_singularPart` provides the uniqueness of the
`singularPart`. Here, the uniqueness is given in terms of the functions, while the uniqueness in
terms of the functions is given in `eq_withDensity_rnDeriv`. -/
theorem eq_rnDeriv [SigmaFinite ν] {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : f =ᵐ[ν] μ.rnDeriv ν :=
  eq_rnDeriv₀ hf.aemeasurable hs hadd
#align measure_theory.measure.eq_rn_deriv MeasureTheory.Measure.eq_rnDeriv

/-- The Radon-Nikodym derivative of `f ν` with respect to `ν` is `f`. -/
theorem rnDeriv_withDensity₀ (ν : Measure α) [SigmaFinite ν] {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f :=
  have : ν.withDensity f = 0 + ν.withDensity f := by rw [zero_add]
  (eq_rnDeriv₀ hf MutuallySingular.zero_left this).symm

/-- The Radon-Nikodym derivative of `f ν` with respect to `ν` is `f`. -/
theorem rnDeriv_withDensity (ν : Measure α) [SigmaFinite ν] {f : α → ℝ≥0∞} (hf : Measurable f) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f :=
  rnDeriv_withDensity₀ ν hf.aemeasurable
#align measure_theory.measure.rn_deriv_with_density MeasureTheory.Measure.rnDeriv_withDensity

lemma rnDeriv_restrict (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] [SigmaFinite ν]
    {s : Set α} (hs : MeasurableSet s) :
    (μ.restrict s).rnDeriv ν =ᵐ[ν] s.indicator (μ.rnDeriv ν) := by
  refine (eq_rnDeriv (s := (μ.restrict s).singularPart ν)
    ((measurable_rnDeriv _ _).indicator hs) (mutuallySingular_singularPart _ _) ?_).symm
  rw [singularPart_restrict _ _ hs, withDensity_indicator hs, ← restrict_withDensity hs,
    ← Measure.restrict_add, ← μ.haveLebesgueDecomposition_add ν]

/-- The Radon-Nikodym derivative of the restriction of a measure to a measurable set is the
indicator function of this set. -/
theorem rnDeriv_restrict_self (ν : Measure α) [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s) :
    (ν.restrict s).rnDeriv ν =ᵐ[ν] s.indicator 1 := by
  rw [← withDensity_indicator_one hs]
  exact rnDeriv_withDensity _ (measurable_one.indicator hs)
#align measure_theory.measure.rn_deriv_restrict MeasureTheory.Measure.rnDeriv_restrict_self

/-- Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left'`, which requires sigma-finite `ν` and `μ`. -/
theorem rnDeriv_smul_left (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] (r : ℝ≥0) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  rw [← withDensity_eq_iff]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices (r • ν).singularPart μ + withDensity μ (rnDeriv (r • ν) μ)
        = (r • ν).singularPart μ + r • withDensity μ (rnDeriv ν μ) by
      rwa [Measure.add_right_inj] at this
    rw [← (r • ν).haveLebesgueDecomposition_add μ, singularPart_smul, ← smul_add,
      ← ν.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _
  · exact (lintegral_rnDeriv_lt_top (r • ν) μ).ne

/-- Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left_of_ne_top'`, which requires sigma-finite `ν` and `μ`. -/
theorem rnDeriv_smul_left_of_ne_top (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : ℝ≥0∞} (hr : r ≠ ∞) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  have h : (r.toNNReal • ν).rnDeriv μ =ᵐ[μ] r.toNNReal • ν.rnDeriv μ :=
    rnDeriv_smul_left ν μ r.toNNReal
  simpa [ENNReal.smul_def, ENNReal.coe_toNNReal hr] using h

/-- Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right'`, which requires sigma-finite `ν` and `μ`. -/
theorem rnDeriv_smul_right (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : ℝ≥0} (hr : r ≠ 0) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  refine (absolutelyContinuous_smul <| ENNReal.coe_ne_zero.2 hr).ae_le
    (?_ : ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ)
  rw [← withDensity_eq_iff]
  rotate_left
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _
  · exact (lintegral_rnDeriv_lt_top ν _).ne
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices ν.singularPart (r • μ) + withDensity (r • μ) (rnDeriv ν (r • μ))
        = ν.singularPart (r • μ) + r⁻¹ • withDensity (r • μ) (rnDeriv ν μ) by
      rwa [add_right_inj] at this
    rw [← ν.haveLebesgueDecomposition_add (r • μ), singularPart_smul_right _ _ _ hr,
      ENNReal.smul_def r, withDensity_smul_measure, ← ENNReal.smul_def, ← smul_assoc,
      smul_eq_mul, inv_mul_cancel hr, one_smul]
    exact ν.haveLebesgueDecomposition_add μ

/-- Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right_of_ne_top'`, which requires sigma-finite `ν` and `μ`. -/
theorem rnDeriv_smul_right_of_ne_top (ν μ : Measure α) [IsFiniteMeasure ν]
    [ν.HaveLebesgueDecomposition μ] {r : ℝ≥0∞} (hr : r ≠ 0) (hr_ne_top : r ≠ ∞) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  have h : ν.rnDeriv (r.toNNReal • μ) =ᵐ[μ] r.toNNReal⁻¹ • ν.rnDeriv μ := by
    refine rnDeriv_smul_right ν μ ?_
    rw [ne_eq, ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  have : (r.toNNReal)⁻¹ • rnDeriv ν μ = r⁻¹ • rnDeriv ν μ := by
    ext x
    simp only [Pi.smul_apply, ENNReal.smul_def, ne_eq, smul_eq_mul]
    rw [ENNReal.coe_inv, ENNReal.coe_toNNReal hr_ne_top]
    rw [ne_eq, ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  simp_rw [this, ENNReal.smul_def, ENNReal.coe_toNNReal hr_ne_top] at h
  exact h

/-- Radon-Nikodym derivative of a sum of two measures.
See also `rnDeriv_add'`, which requires sigma-finite `ν₁`, `ν₂` and `μ`. -/
lemma rnDeriv_add (ν₁ ν₂ μ : Measure α) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂]
    [ν₁.HaveLebesgueDecomposition μ] [ν₂.HaveLebesgueDecomposition μ]
    [(ν₁ + ν₂).HaveLebesgueDecomposition μ] :
    (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ + ν₂.rnDeriv μ := by
  rw [← withDensity_eq_iff]
  · suffices (ν₁ + ν₂).singularPart μ + μ.withDensity ((ν₁ + ν₂).rnDeriv μ)
        = (ν₁ + ν₂).singularPart μ + μ.withDensity (ν₁.rnDeriv μ + ν₂.rnDeriv μ) by
      rwa [add_right_inj] at this
    rw [← (ν₁ + ν₂).haveLebesgueDecomposition_add μ, singularPart_add,
      withDensity_add_left (measurable_rnDeriv _ _), add_assoc,
      add_comm (ν₂.singularPart μ), add_assoc, add_comm _ (ν₂.singularPart μ),
      ← ν₂.haveLebesgueDecomposition_add μ, ← add_assoc, ← ν₁.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact ((measurable_rnDeriv _ _).add (measurable_rnDeriv _ _)).aemeasurable
  · exact (lintegral_rnDeriv_lt_top (ν₁ + ν₂) μ).ne

open VectorMeasure SignedMeasure

/-- If two finite measures `μ` and `ν` are not mutually singular, there exists some `ε > 0` and
a measurable set `E`, such that `ν(E) > 0` and `E` is positive with respect to `μ - εν`.

This lemma is useful for the Lebesgue decomposition theorem. -/
theorem exists_positive_of_not_mutuallySingular (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (h : ¬μ ⟂ₘ ν) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∃ E : Set α,
        MeasurableSet E ∧ 0 < ν E ∧ 0 ≤[E] μ.toSignedMeasure - (ε • ν).toSignedMeasure := by
  -- for all `n : ℕ`, obtain the Hahn decomposition for `μ - (1 / n) ν`
  have :
    ∀ n : ℕ, ∃ i : Set α,
      MeasurableSet i ∧
        0 ≤[i] μ.toSignedMeasure - ((1 / (n + 1) : ℝ≥0) • ν).toSignedMeasure ∧
          μ.toSignedMeasure - ((1 / (n + 1) : ℝ≥0) • ν).toSignedMeasure ≤[iᶜ] 0 := by
    intro; exact exists_compl_positive_negative _
  choose f hf₁ hf₂ hf₃ using this
  -- set `A` to be the intersection of all the negative parts of obtained Hahn decompositions
  -- and we show that `μ A = 0`
  set A := ⋂ n, (f n)ᶜ with hA₁
  have hAmeas : MeasurableSet A := MeasurableSet.iInter fun n ↦ (hf₁ n).compl
  have hA₂ : ∀ n : ℕ, μ.toSignedMeasure - ((1 / (n + 1) : ℝ≥0) • ν).toSignedMeasure ≤[A] 0 := by
    intro n; exact restrict_le_restrict_subset _ _ (hf₁ n).compl (hf₃ n) (iInter_subset _ _)
  have hA₃ : ∀ n : ℕ, μ A ≤ (1 / (n + 1) : ℝ≥0) * ν A := by
    intro n
    have := nonpos_of_restrict_le_zero _ (hA₂ n)
    rwa [toSignedMeasure_sub_apply hAmeas, sub_nonpos, ENNReal.toReal_le_toReal] at this
    exacts [measure_ne_top _ _, measure_ne_top _ _]
  have hμ : μ A = 0 := by
    lift μ A to ℝ≥0 using measure_ne_top _ _ with μA
    lift ν A to ℝ≥0 using measure_ne_top _ _ with νA
    rw [ENNReal.coe_eq_zero]
    by_cases hb : 0 < νA
    · suffices ∀ b, 0 < b → μA ≤ b by
        by_contra h
        have h' := this (μA / 2) (half_pos (zero_lt_iff.2 h))
        rw [← @Classical.not_not (μA ≤ μA / 2)] at h'
        exact h' (not_le.2 (NNReal.half_lt_self h))
      intro c hc
      have : ∃ n : ℕ, 1 / (n + 1 : ℝ) < c * (νA : ℝ)⁻¹ := by
        refine exists_nat_one_div_lt ?_
        positivity
      rcases this with ⟨n, hn⟩
      have hb₁ : (0 : ℝ) < (νA : ℝ)⁻¹ := by rw [_root_.inv_pos]; exact hb
      have h' : 1 / (↑n + 1) * νA < c := by
        rw [← NNReal.coe_lt_coe, ← mul_lt_mul_right hb₁, NNReal.coe_mul, mul_assoc, ←
          NNReal.coe_inv, ← NNReal.coe_mul, _root_.mul_inv_cancel, ← NNReal.coe_mul, mul_one,
          NNReal.coe_inv]
        · exact hn
        · exact hb.ne'
      refine le_trans ?_ h'.le
      rw [← ENNReal.coe_le_coe, ENNReal.coe_mul]
      exact hA₃ n
    · rw [not_lt, le_zero_iff] at hb
      specialize hA₃ 0
      simp? [hb] at hA₃ says
        simp only [CharP.cast_eq_zero, zero_add, ne_eq, one_ne_zero, not_false_eq_true, div_self,
          ENNReal.coe_one, hb, ENNReal.coe_zero, mul_zero, nonpos_iff_eq_zero,
          ENNReal.coe_eq_zero] at hA₃
      assumption
  -- since `μ` and `ν` are not mutually singular, `μ A = 0` implies `ν Aᶜ > 0`
  rw [MutuallySingular] at h; push_neg at h
  have := h _ hAmeas hμ
  simp_rw [A, compl_iInter, compl_compl] at this
  -- as `Aᶜ = ⋃ n, f n`, `ν Aᶜ > 0` implies there exists some `n` such that `ν (f n) > 0`
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null this
  -- thus, choosing `f n` as the set `E` suffices
  exact ⟨1 / (n + 1), by simp, f n, hf₁ n, hn, hf₂ n⟩
#align measure_theory.measure.exists_positive_of_not_mutually_singular MeasureTheory.Measure.exists_positive_of_not_mutuallySingular

namespace LebesgueDecomposition

/-- Given two measures `μ` and `ν`, `measurableLE μ ν` is the set of measurable
functions `f`, such that, for all measurable sets `A`, `∫⁻ x in A, f x ∂μ ≤ ν A`.

This is useful for the Lebesgue decomposition theorem. -/
def measurableLE (μ ν : Measure α) : Set (α → ℝ≥0∞) :=
  {f | Measurable f ∧ ∀ (A : Set α), MeasurableSet A → (∫⁻ x in A, f x ∂μ) ≤ ν A}
#align measure_theory.measure.lebesgue_decomposition.measurable_le MeasureTheory.Measure.LebesgueDecomposition.measurableLE

theorem zero_mem_measurableLE : (0 : α → ℝ≥0∞) ∈ measurableLE μ ν :=
  ⟨measurable_zero, fun A _ ↦ by simp⟩
#align measure_theory.measure.lebesgue_decomposition.zero_mem_measurable_le MeasureTheory.Measure.LebesgueDecomposition.zero_mem_measurableLE

theorem sup_mem_measurableLE {f g : α → ℝ≥0∞} (hf : f ∈ measurableLE μ ν)
    (hg : g ∈ measurableLE μ ν) : (fun a ↦ f a ⊔ g a) ∈ measurableLE μ ν := by
  simp_rw [ENNReal.sup_eq_max]
  refine ⟨Measurable.max hf.1 hg.1, fun A hA ↦ ?_⟩
  have h₁ := hA.inter (measurableSet_le hf.1 hg.1)
  have h₂ := hA.inter (measurableSet_lt hg.1 hf.1)
  rw [set_lintegral_max hf.1 hg.1]
  refine (add_le_add (hg.2 _ h₁) (hf.2 _ h₂)).trans_eq ?_
  simp only [← not_le, ← compl_setOf, ← diff_eq]
  exact measure_inter_add_diff _ (measurableSet_le hf.1 hg.1)
#align measure_theory.measure.lebesgue_decomposition.sup_mem_measurable_le MeasureTheory.Measure.LebesgueDecomposition.sup_mem_measurableLE

theorem iSup_succ_eq_sup {α} (f : ℕ → α → ℝ≥0∞) (m : ℕ) (a : α) :
    ⨆ (k : ℕ) (_ : k ≤ m + 1), f k a = f m.succ a ⊔ ⨆ (k : ℕ) (_ : k ≤ m), f k a := by
  set c := ⨆ (k : ℕ) (_ : k ≤ m + 1), f k a with hc
  set d := f m.succ a ⊔ ⨆ (k : ℕ) (_ : k ≤ m), f k a with hd
  rw [le_antisymm_iff, hc, hd]
  constructor
  · refine iSup₂_le fun n hn ↦ ?_
    rcases Nat.of_le_succ hn with (h | h)
    · exact le_sup_of_le_right (le_iSup₂ (f := fun k (_ : k ≤ m) ↦ f k a) n h)
    · exact h ▸ le_sup_left
  · refine sup_le ?_ (biSup_mono fun n hn ↦ hn.trans m.le_succ)
    exact @le_iSup₂ ℝ≥0∞ ℕ (fun i ↦ i ≤ m + 1) _ _ (m + 1) le_rfl
#align measure_theory.measure.lebesgue_decomposition.supr_succ_eq_sup MeasureTheory.Measure.LebesgueDecomposition.iSup_succ_eq_sup

theorem iSup_mem_measurableLE (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurableLE μ ν) (n : ℕ) :
    (fun x ↦ ⨆ (k) (_ : k ≤ n), f k x) ∈ measurableLE μ ν := by
  induction' n with m hm
  · constructor
    · simp [(hf 0).1]
    · intro A hA; simp [(hf 0).2 A hA]
  · have :
      (fun a : α ↦ ⨆ (k : ℕ) (_ : k ≤ m + 1), f k a) = fun a ↦
        f m.succ a ⊔ ⨆ (k : ℕ) (_ : k ≤ m), f k a :=
      funext fun _ ↦ iSup_succ_eq_sup _ _ _
    refine ⟨measurable_iSup fun n ↦ Measurable.iSup_Prop _ (hf n).1, fun A hA ↦ ?_⟩
    rw [this]; exact (sup_mem_measurableLE (hf m.succ) hm).2 A hA
#align measure_theory.measure.lebesgue_decomposition.supr_mem_measurable_le MeasureTheory.Measure.LebesgueDecomposition.iSup_mem_measurableLE

theorem iSup_mem_measurableLE' (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurableLE μ ν) (n : ℕ) :
    (⨆ (k) (_ : k ≤ n), f k) ∈ measurableLE μ ν := by
  convert iSup_mem_measurableLE f hf n
  simp
#align measure_theory.measure.lebesgue_decomposition.supr_mem_measurable_le' MeasureTheory.Measure.LebesgueDecomposition.iSup_mem_measurableLE'

section SuprLemmas

--TODO: these statements should be moved elsewhere

theorem iSup_monotone {α : Type*} (f : ℕ → α → ℝ≥0∞) :
    Monotone fun n x ↦ ⨆ (k) (_ : k ≤ n), f k x :=
  fun _ _ hnm _ ↦ biSup_mono fun _ ↦ ge_trans hnm
#align measure_theory.measure.lebesgue_decomposition.supr_monotone MeasureTheory.Measure.LebesgueDecomposition.iSup_monotone

theorem iSup_monotone' {α : Type*} (f : ℕ → α → ℝ≥0∞) (x : α) :
    Monotone fun n ↦ ⨆ (k) (_ : k ≤ n), f k x := fun _ _ hnm ↦ iSup_monotone f hnm x
#align measure_theory.measure.lebesgue_decomposition.supr_monotone' MeasureTheory.Measure.LebesgueDecomposition.iSup_monotone'

theorem iSup_le_le {α : Type*} (f : ℕ → α → ℝ≥0∞) (n k : ℕ) (hk : k ≤ n) :
    f k ≤ fun x ↦ ⨆ (k) (_ : k ≤ n), f k x :=
  fun x ↦ le_iSup₂ (f := fun k (_ : k ≤ n) ↦ f k x) k hk
#align measure_theory.measure.lebesgue_decomposition.supr_le_le MeasureTheory.Measure.LebesgueDecomposition.iSup_le_le

end SuprLemmas

/-- `measurableLEEval μ ν` is the set of `∫⁻ x, f x ∂μ` for all `f ∈ measurableLE μ ν`. -/
def measurableLEEval (μ ν : Measure α) : Set ℝ≥0∞ :=
  (fun f : α → ℝ≥0∞ ↦ ∫⁻ x, f x ∂μ) '' measurableLE μ ν
#align measure_theory.measure.lebesgue_decomposition.measurable_le_eval MeasureTheory.Measure.LebesgueDecomposition.measurableLEEval

end LebesgueDecomposition

open LebesgueDecomposition

/-- Any pair of finite measures `μ` and `ν`, `HaveLebesgueDecomposition`. That is to say,
there exist a measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular
with respect to `ν` and `μ = ξ + ν.withDensity f`.

This is not an instance since this is also shown for the more general σ-finite measures with
`MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`. -/
theorem haveLebesgueDecomposition_of_finiteMeasure [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    HaveLebesgueDecomposition μ ν :=
  ⟨by
    have h := @exists_seq_tendsto_sSup _ _ _ _ _ (measurableLEEval ν μ)
      ⟨0, 0, zero_mem_measurableLE, by simp⟩ (OrderTop.bddAbove _)
    choose g _ hg₂ f hf₁ hf₂ using h
    -- we set `ξ` to be the supremum of an increasing sequence of functions obtained from above
    set ξ := ⨆ (n) (k) (_ : k ≤ n), f k with hξ
    -- we see that `ξ` has the largest integral among all functions in `measurableLE`
    have hξ₁ : sSup (measurableLEEval ν μ) = ∫⁻ a, ξ a ∂ν := by
      have :=
        @lintegral_tendsto_of_tendsto_of_monotone _ _ ν (fun n ↦ ⨆ (k) (_ : k ≤ n), f k)
          (⨆ (n) (k) (_ : k ≤ n), f k) ?_ ?_ ?_
      · refine tendsto_nhds_unique ?_ this
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg₂ tendsto_const_nhds ?_ ?_
        · intro n; rw [← hf₂ n]
          apply lintegral_mono
          simp only [iSup_apply, iSup_le_le f n n le_rfl]
        · intro n
          exact le_sSup ⟨⨆ (k : ℕ) (_ : k ≤ n), f k, iSup_mem_measurableLE' _ hf₁ _, rfl⟩
      · intro n
        refine Measurable.aemeasurable ?_
        convert (iSup_mem_measurableLE _ hf₁ n).1
        simp
      · refine Filter.eventually_of_forall fun a ↦ ?_
        simp [iSup_monotone' f _]
      · refine Filter.eventually_of_forall fun a ↦ ?_
        simp [tendsto_atTop_iSup (iSup_monotone' f a)]
    have hξm : Measurable ξ := by
      convert measurable_iSup fun n ↦ (iSup_mem_measurableLE _ hf₁ n).1
      simp [hξ]
    -- `ξ` is the `f` in the theorem statement and we set `μ₁` to be `μ - ν.withDensity ξ`
    -- since we need `μ₁ + ν.withDensity ξ = μ`
    set μ₁ := μ - ν.withDensity ξ with hμ₁
    have hle : ν.withDensity ξ ≤ μ := by
      refine le_iff.2 fun B hB ↦ ?_
      rw [hξ, withDensity_apply _ hB]
      simp_rw [iSup_apply]
      rw [lintegral_iSup (fun i ↦ (iSup_mem_measurableLE _ hf₁ i).1) (iSup_monotone _)]
      exact iSup_le fun i ↦ (iSup_mem_measurableLE _ hf₁ i).2 B hB
    have : IsFiniteMeasure (ν.withDensity ξ) := by
      refine isFiniteMeasure_withDensity ?_
      have hle' := hle univ
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hle'
      exact ne_top_of_le_ne_top (measure_ne_top _ _) hle'
    refine ⟨⟨μ₁, ξ⟩, hξm, ?_, ?_⟩
    · by_contra h
      -- if they are not mutually singular, then from `exists_positive_of_not_mutuallySingular`,
      -- there exists some `ε > 0` and a measurable set `E`, such that `μ(E) > 0` and `E` is
      -- positive with respect to `ν - εμ`
      obtain ⟨ε, hε₁, E, hE₁, hE₂, hE₃⟩ := exists_positive_of_not_mutuallySingular μ₁ ν h
      simp_rw [hμ₁] at hE₃
      have hξle : ∀ A, MeasurableSet A → (∫⁻ a in A, ξ a ∂ν) ≤ μ A := by
        intro A hA; rw [hξ]
        simp_rw [iSup_apply]
        rw [lintegral_iSup (fun n ↦ (iSup_mem_measurableLE _ hf₁ n).1) (iSup_monotone _)]
        exact iSup_le fun n ↦ (iSup_mem_measurableLE _ hf₁ n).2 A hA
      -- since `E` is positive, we have `∫⁻ a in A ∩ E, ε + ξ a ∂ν ≤ μ (A ∩ E)` for all `A`
      have hε₂ : ∀ A : Set α, MeasurableSet A → (∫⁻ a in A ∩ E, ε + ξ a ∂ν) ≤ μ (A ∩ E) := by
        intro A hA
        have := subset_le_of_restrict_le_restrict _ _ hE₁ hE₃ A.inter_subset_right
        rwa [zero_apply, toSignedMeasure_sub_apply (hA.inter hE₁),
          Measure.sub_apply (hA.inter hE₁) hle,
          ENNReal.toReal_sub_of_le _ (measure_ne_top _ _), sub_nonneg, le_sub_iff_add_le,
          ← ENNReal.toReal_add, ENNReal.toReal_le_toReal, Measure.coe_smul, Pi.smul_apply,
          withDensity_apply _ (hA.inter hE₁), show ε • ν (A ∩ E) = (ε : ℝ≥0∞) * ν (A ∩ E) by rfl,
          ← set_lintegral_const, ← lintegral_add_left measurable_const] at this
        · rw [Ne, ENNReal.add_eq_top, not_or]
          exact ⟨measure_ne_top _ _, measure_ne_top _ _⟩
        · exact measure_ne_top _ _
        · exact measure_ne_top _ _
        · exact measure_ne_top _ _
        · rw [withDensity_apply _ (hA.inter hE₁)]
          exact hξle (A ∩ E) (hA.inter hE₁)
      -- from this, we can show `ξ + ε * E.indicator` is a function in `measurableLE` with
      -- integral greater than `ξ`
      have hξε : (ξ + E.indicator fun _ ↦ (ε : ℝ≥0∞)) ∈ measurableLE ν μ := by
        refine ⟨Measurable.add hξm (Measurable.indicator measurable_const hE₁), fun A hA ↦ ?_⟩
        have :
          (∫⁻ a in A, (ξ + E.indicator fun _ ↦ (ε : ℝ≥0∞)) a ∂ν) =
            (∫⁻ a in A ∩ E, ε + ξ a ∂ν) + ∫⁻ a in A \ E, ξ a ∂ν := by
          simp only [lintegral_add_left measurable_const, lintegral_add_left hξm,
            set_lintegral_const, add_assoc, lintegral_inter_add_diff _ _ hE₁, Pi.add_apply,
            lintegral_indicator _ hE₁, restrict_apply hE₁]
          rw [inter_comm, add_comm]
        rw [this, ← measure_inter_add_diff A hE₁]
        exact add_le_add (hε₂ A hA) (hξle (A \ E) (hA.diff hE₁))
      have : (∫⁻ a, ξ a + E.indicator (fun _ ↦ (ε : ℝ≥0∞)) a ∂ν) ≤ sSup (measurableLEEval ν μ) :=
        le_sSup ⟨ξ + E.indicator fun _ ↦ (ε : ℝ≥0∞), hξε, rfl⟩
      -- but this contradicts the maximality of `∫⁻ x, ξ x ∂ν`
      refine not_lt.2 this ?_
      rw [hξ₁, lintegral_add_left hξm, lintegral_indicator _ hE₁, set_lintegral_const]
      refine ENNReal.lt_add_right ?_ (ENNReal.mul_pos_iff.2 ⟨ENNReal.coe_pos.2 hε₁, hE₂⟩).ne'
      have := measure_ne_top (ν.withDensity ξ) univ
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    -- since `ν.withDensity ξ ≤ μ`, it is clear that `μ = μ₁ + ν.withDensity ξ`
    · rw [hμ₁]; ext1 A hA
      rw [Measure.coe_add, Pi.add_apply, Measure.sub_apply hA hle, add_comm,
        add_tsub_cancel_of_le (hle A)]⟩
#align measure_theory.measure.have_lebesgue_decomposition_of_finite_measure MeasureTheory.Measure.haveLebesgueDecomposition_of_finiteMeasure

attribute [local instance] haveLebesgueDecomposition_of_finiteMeasure

instance restrict.instIsFiniteMeasure {S : μ.FiniteSpanningSetsIn {s : Set α | MeasurableSet s}}
    (n : ℕ) : IsFiniteMeasure (μ.restrict <| S.set n) :=
  ⟨by rw [restrict_apply MeasurableSet.univ, univ_inter]; exact S.finite _⟩
#align measure_theory.measure.restrict.measure_theory.is_finite_measure MeasureTheory.Measure.restrict.instIsFiniteMeasure

-- see Note [lower instance priority]
/-- **The Lebesgue decomposition theorem**: Any pair of σ-finite measures `μ` and `ν`
`HaveLebesgueDecomposition`. That is to say, there exist a measure `ξ` and a measurable function
`f`, such that `ξ` is mutually singular with respect to `ν` and `μ = ξ + ν.withDensity f` -/
instance (priority := 100) haveLebesgueDecomposition_of_sigmaFinite (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] : HaveLebesgueDecomposition μ ν :=
  ⟨by
    -- Since `μ` and `ν` are both σ-finite, there exists a sequence of pairwise disjoint spanning
    -- sets which are finite with respect to both `μ` and `ν`
    obtain ⟨S, T, h₁, h₂⟩ := exists_eq_disjoint_finiteSpanningSetsIn μ ν
    have h₃ : Pairwise (Disjoint on T.set) := h₁ ▸ h₂
    -- We define `μn` and `νn` as sequences of measures such that `μn n = μ ∩ S n` and
    -- `νn n = ν ∩ S n` where `S` is the aforementioned finite spanning set sequence.
    -- Since `S` is spanning, it is clear that `sum μn = μ` and `sum νn = ν`
    set μn : ℕ → Measure α := fun n ↦ μ.restrict (S.set n) with hμn
    have hμ : μ = sum μn := by rw [hμn, ← restrict_iUnion h₂ S.set_mem, S.spanning, restrict_univ]
    set νn : ℕ → Measure α := fun n ↦ ν.restrict (T.set n) with hνn
    have hν : ν = sum νn := by rw [hνn, ← restrict_iUnion h₃ T.set_mem, T.spanning, restrict_univ]
    -- As `S` is finite with respect to both `μ` and `ν`, it is clear that `μn n` and `νn n` are
    -- finite measures for all `n : ℕ`. Thus, we may apply the finite Lebesgue decomposition theorem
    -- to `μn n` and `νn n`. We define `ξ` as the sum of the singular part of the Lebesgue
    -- decompositions of `μn n` and `νn n`, and `f` as the sum of the Radon-Nikodym derivatives of
    -- `μn n` and `νn n` restricted on `S n`
    set ξ := sum fun n ↦ singularPart (μn n) (νn n) with hξ
    set f := ∑' n, (S.set n).indicator (rnDeriv (μn n) (νn n))
    -- I claim `ξ` and `f` form a Lebesgue decomposition of `μ` and `ν`
    refine ⟨⟨ξ, f⟩, ?_, ?_, ?_⟩
    · exact Measurable.ennreal_tsum'
        fun n ↦ Measurable.indicator (measurable_rnDeriv (μn n) (νn n)) (S.set_mem n)
    -- We show that `ξ` is mutually singular with respect to `ν`
    · choose A hA₁ hA₂ hA₃ using fun n ↦ mutuallySingular_singularPart (μn n) (νn n)
      simp only [hξ]
      -- We use the set `B := ⋃ j, (S.set j) ∩ A j` where `A n` is the set provided as
      -- `singularPart (μn n) (νn n) ⟂ₘ νn n`
      refine ⟨⋃ j, S.set j ∩ A j, MeasurableSet.iUnion fun n ↦ (S.set_mem n).inter (hA₁ n), ?_, ?_⟩
      -- `ξ B = 0` since `ξ B = ∑ i j, singularPart (μn j) (νn j) (S.set i ∩ A i)`
      --                     `= ∑ i, singularPart (μn i) (νn i) (S.set i ∩ A i)`
      --                     `≤ ∑ i, singularPart (μn i) (νn i) (A i) = 0`
      -- where the second equality follows as `singularPart (μn j) (νn j) (S.set i ∩ A i)` vanishes
      -- for all `i ≠ j`
      · rw [measure_iUnion]
        · have : ∀ i, (sum fun n ↦ (μn n).singularPart (νn n)) (S.set i ∩ A i)
              = (μn i).singularPart (νn i) (S.set i ∩ A i) := by
            intro i; rw [sum_apply _ ((S.set_mem i).inter (hA₁ i)), tsum_eq_single i]
            · intro j hij
              rw [hμn, ← nonpos_iff_eq_zero]
              refine (singularPart_le _ _ _).trans_eq ?_
              rw [restrict_apply ((S.set_mem i).inter (hA₁ i)), inter_comm, ← inter_assoc]
              have : Disjoint (S.set j) (S.set i) := h₂ hij
              rw [disjoint_iff_inter_eq_empty] at this
              rw [this, empty_inter, measure_empty]
          simp_rw [this, tsum_eq_zero_iff ENNReal.summable]
          intro n; exact measure_mono_null inter_subset_right (hA₂ n)
        · exact h₂.mono fun i j ↦ Disjoint.mono inf_le_left inf_le_left
        · exact fun n ↦ (S.set_mem n).inter (hA₁ n)
      -- We will now show `ν Bᶜ = 0`. This follows since `Bᶜ = ⋃ n, S.set n ∩ (A n)ᶜ` and thus,
      -- `ν Bᶜ = ∑ i, ν (S.set i ∩ (A i)ᶜ) = ∑ i, (νn i) (A i)ᶜ = 0`
      · have hcompl : IsCompl (⋃ n, S.set n ∩ A n) (⋃ n, S.set n ∩ (A n)ᶜ) := by
          constructor
          · rw [disjoint_iff_inf_le]
            rintro x ⟨hx₁, hx₂⟩; rw [mem_iUnion] at hx₁ hx₂
            obtain ⟨⟨i, hi₁, hi₂⟩, ⟨j, hj₁, hj₂⟩⟩ := hx₁, hx₂
            have : i = j := by by_contra hij; exact (h₂ hij).le_bot ⟨hi₁, hj₁⟩
            exact hj₂ (this ▸ hi₂)
          · rw [codisjoint_iff_le_sup]
            intro x hx
            simp only [mem_iUnion, sup_eq_union, mem_inter_iff, mem_union, mem_compl_iff,
              or_iff_not_imp_left]
            intro h; push_neg at h
            rw [top_eq_univ, ← S.spanning, mem_iUnion] at hx
            obtain ⟨i, hi⟩ := hx
            exact ⟨i, hi, h i hi⟩
        rw [hcompl.compl_eq, measure_iUnion, tsum_eq_zero_iff ENNReal.summable]
        · intro n; rw [inter_comm, ← restrict_apply (hA₁ n).compl, ← hA₃ n, hνn, h₁]
        · exact h₂.mono fun i j ↦ Disjoint.mono inf_le_left inf_le_left
        · exact fun n ↦ (S.set_mem n).inter (hA₁ n).compl
    -- Finally, it remains to show `μ = ξ + ν.withDensity f`. Since `μ = sum μn`, and
    -- `ξ + ν.withDensity f = ∑ n, singularPart (μn n) (νn n)`
    --                        `+ ν.withDensity (rnDeriv (μn n) (νn n)) ∩ (S.set n)`,
    -- it suffices to show that the individual summands are equal. This follows by the
    -- Lebesgue decomposition properties on the individual `μn n` and `νn n`
    · simp only
      nth_rw 1 [hμ]
      rw [withDensity_tsum _, sum_add_sum]
      · refine sum_congr fun n ↦ ?_
        nth_rw 1 [haveLebesgueDecomposition_add (μn n) (νn n)]
        suffices heq :
          (νn n).withDensity ((μn n).rnDeriv (νn n)) =
            ν.withDensity ((S.set n).indicator ((μn n).rnDeriv (νn n))) by rw [heq]
        rw [hν, withDensity_indicator (S.set_mem n), restrict_sum _ (S.set_mem n)]
        suffices hsumeq : (sum fun i : ℕ ↦ (νn i).restrict (S.set n)) = νn n by rw [hsumeq]
        ext1 s hs
        rw [sum_apply _ hs, tsum_eq_single n, hνn, h₁, restrict_restrict (T.set_mem n), inter_self]
        intro m hm
        rw [hνn, h₁, restrict_restrict (T.set_mem n), (h₃ hm.symm).inter_eq, restrict_empty,
          coe_zero, Pi.zero_apply]
      · exact fun n ↦ Measurable.indicator (measurable_rnDeriv _ _) (S.set_mem n)⟩
#align measure_theory.measure.have_lebesgue_decomposition_of_sigma_finite MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite

section rnDeriv

/-- Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left`, which has no hypothesis on `μ` but requires finite `ν`. -/
theorem rnDeriv_smul_left' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ] (r : ℝ≥0) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices (r • ν).singularPart μ + withDensity μ (rnDeriv (r • ν) μ)
        = (r • ν).singularPart μ + r • withDensity μ (rnDeriv ν μ) by
      rwa [Measure.add_right_inj] at this
    rw [← (r • ν).haveLebesgueDecomposition_add μ, singularPart_smul, ← smul_add,
      ← ν.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _

/-- Radon-Nikodym derivative of the scalar multiple of a measure.
See also `rnDeriv_smul_left_of_ne_top`, which has no hypothesis on `μ` but requires finite `ν`. -/
theorem rnDeriv_smul_left_of_ne_top' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
    {r : ℝ≥0∞} (hr : r ≠ ∞) :
    (r • ν).rnDeriv μ =ᵐ[μ] r • ν.rnDeriv μ := by
  have h : (r.toNNReal • ν).rnDeriv μ =ᵐ[μ] r.toNNReal • ν.rnDeriv μ :=
    rnDeriv_smul_left' ν μ r.toNNReal
  simpa [ENNReal.smul_def, ENNReal.coe_toNNReal hr] using h

/-- Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right`, which has no hypothesis on `μ` but requires finite `ν`. -/
theorem rnDeriv_smul_right' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
    {r : ℝ≥0} (hr : r ≠ 0) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  refine (absolutelyContinuous_smul <| ENNReal.coe_ne_zero.2 hr).ae_le
    (?_ : ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ)
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · simp_rw [ENNReal.smul_def]
    rw [withDensity_smul _ (measurable_rnDeriv _ _)]
    suffices ν.singularPart (r • μ) + withDensity (r • μ) (rnDeriv ν (r • μ))
        = ν.singularPart (r • μ) + r⁻¹ • withDensity (r • μ) (rnDeriv ν μ) by
      rwa [add_right_inj] at this
    rw [← ν.haveLebesgueDecomposition_add (r • μ), singularPart_smul_right _ _ _ hr,
      ENNReal.smul_def r, withDensity_smul_measure, ← ENNReal.smul_def, ← smul_assoc,
      smul_eq_mul, inv_mul_cancel hr, one_smul]
    exact ν.haveLebesgueDecomposition_add μ
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact (measurable_rnDeriv _ _).aemeasurable.const_smul _

/-- Radon-Nikodym derivative with respect to the scalar multiple of a measure.
See also `rnDeriv_smul_right_of_ne_top`, which has no hypothesis on `μ` but requires finite `ν`. -/
theorem rnDeriv_smul_right_of_ne_top' (ν μ : Measure α) [SigmaFinite ν] [SigmaFinite μ]
    {r : ℝ≥0∞} (hr : r ≠ 0) (hr_ne_top : r ≠ ∞) :
    ν.rnDeriv (r • μ) =ᵐ[μ] r⁻¹ • ν.rnDeriv μ := by
  have h : ν.rnDeriv (r.toNNReal • μ) =ᵐ[μ] r.toNNReal⁻¹ • ν.rnDeriv μ := by
    refine rnDeriv_smul_right' ν μ ?_
    rw [ne_eq, ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  rwa [ENNReal.smul_def, ENNReal.coe_toNNReal hr_ne_top,
    ← ENNReal.toNNReal_inv, ENNReal.smul_def, ENNReal.coe_toNNReal (ENNReal.inv_ne_top.mpr hr)] at h

/-- Radon-Nikodym derivative of a sum of two measures.
See also `rnDeriv_add`, which has no hypothesis on `μ` but requires finite `ν₁` and `ν₂`. -/
lemma rnDeriv_add' (ν₁ ν₂ μ : Measure α) [SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] :
    (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ + ν₂.rnDeriv μ := by
  rw [← withDensity_eq_iff_of_sigmaFinite]
  · suffices (ν₁ + ν₂).singularPart μ + μ.withDensity ((ν₁ + ν₂).rnDeriv μ)
        = (ν₁ + ν₂).singularPart μ + μ.withDensity (ν₁.rnDeriv μ + ν₂.rnDeriv μ) by
      rwa [add_right_inj] at this
    rw [← (ν₁ + ν₂).haveLebesgueDecomposition_add μ, singularPart_add,
      withDensity_add_left (measurable_rnDeriv _ _), add_assoc,
      add_comm (ν₂.singularPart μ), add_assoc, add_comm _ (ν₂.singularPart μ),
      ← ν₂.haveLebesgueDecomposition_add μ, ← add_assoc, ← ν₁.haveLebesgueDecomposition_add μ]
  · exact (measurable_rnDeriv _ _).aemeasurable
  · exact ((measurable_rnDeriv _ _).add (measurable_rnDeriv _ _)).aemeasurable

lemma rnDeriv_add_of_mutuallySingular (ν₁ ν₂ μ : Measure α)
    [SigmaFinite ν₁] [SigmaFinite ν₂] [SigmaFinite μ] (h : ν₂ ⟂ₘ μ) :
    (ν₁ + ν₂).rnDeriv μ =ᵐ[μ] ν₁.rnDeriv μ := by
  filter_upwards [rnDeriv_add' ν₁ ν₂ μ, (rnDeriv_eq_zero ν₂ μ).mpr h] with x hx_add hx_zero
  simp [hx_add, hx_zero]

end rnDeriv

end Measure

end MeasureTheory
