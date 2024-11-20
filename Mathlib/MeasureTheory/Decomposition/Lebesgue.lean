/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Decomposition.LebesgueDecomposition
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.L1Space

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

variable {α : Type*} {m : MeasurableSpace α} {μ ν : Measure α}

lemma _root_.AEMeasurable.singularPart {β : Type*} {_ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (ν : Measure α) :
    AEMeasurable f (μ.singularPart ν) :=
  AEMeasurable.mono_measure hf (Measure.singularPart_le _ _)

lemma _root_.AEMeasurable.withDensity_rnDeriv {β : Type*} {_ : MeasurableSpace β} {f : α → β}
    (hf : AEMeasurable f μ) (ν : Measure α) :
    AEMeasurable f (ν.withDensity (μ.rnDeriv ν)) :=
  AEMeasurable.mono_measure hf (Measure.withDensity_rnDeriv_le _ _)

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

theorem lintegral_rnDeriv_lt_top (μ ν : Measure α) [IsFiniteMeasure μ] :
    ∫⁻ x, μ.rnDeriv ν x ∂ν < ∞ := by
  rw [← setLIntegral_univ]
  exact lintegral_rnDeriv_lt_top_of_measure_ne_top _ (measure_lt_top _ _).ne

--todo: this is the only lemma that requires `import Mathlib.MeasureTheory.Function.L1Space`
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
  rw [← ae_restrict_iff' (measurableSet_spanningSets _ _)]
  apply ae_lt_top (measurable_rnDeriv _ _)
  refine (lintegral_rnDeriv_lt_top_of_measure_ne_top _ ?_).ne
  exact (measure_spanningSets_lt_top _ _).ne

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
      smul_eq_mul, inv_mul_cancel₀ hr, one_smul]
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
      smul_eq_mul, inv_mul_cancel₀ hr, one_smul]
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
