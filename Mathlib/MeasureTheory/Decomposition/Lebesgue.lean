/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
import Mathlib.MeasureTheory.Measure.Complex
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Decomposition.Jordan
import Mathlib.MeasureTheory.Measure.WithDensityVectorMeasure
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
* `MeasureTheory.SignedMeasure.HaveLebesgueDecomposition` : A signed measure `s` and a
  measure `μ` is said to `HaveLebesgueDecomposition` if both the positive part and negative
  part of `s` `HaveLebesgueDecomposition` with respect to `μ`.
* `MeasureTheory.SignedMeasure.singularPart` : The singular part between a signed measure `s`
  and a measure `μ` is simply the singular part of the positive part of `s` with respect to `μ`
  minus the singular part of the negative part of `s` with respect to `μ`.
* `MeasureTheory.SignedMeasure.rnDeriv` : The Radon-Nikodym derivative of a signed
  measure `s` with respect to a measure `μ` is the Radon-Nikodym derivative of the positive part of
  `s` with respect to `μ` minus the Radon-Nikodym derivative of the negative part of `s` with
  respect to `μ`.

## Main results

* `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite` :
  the Lebesgue decomposition theorem.
* `MeasureTheory.Measure.eq_singularPart` : Given measures `μ` and `ν`, if `s` is a measure
  mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`, then
  `s = μ.singularPart ν`.
* `MeasureTheory.Measure.eq_rnDeriv` : Given measures `μ` and `ν`, if `s` is a
  measure mutually singular to `ν` and `f` is a measurable function such that `μ = s + fν`,
  then `f = μ.rnDeriv ν`.
* `MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq` :
  the Lebesgue decomposition theorem between a signed measure and a σ-finite positive measure.

# Tags

Lebesgue decomposition theorem
-/


noncomputable section

open scoped Classical MeasureTheory NNReal ENNReal

open Set

variable {α β : Type*} {m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α}

namespace MeasureTheory

namespace Measure

/-- A pair of measures `μ` and `ν` is said to `HaveLebesgueDecomposition` if there exists a
measure `ξ` and a measurable function `f`, such that `ξ` is mutually singular with respect to
`ν` and `μ = ξ + ν.withDensity f`. -/
class HaveLebesgueDecomposition (μ ν : Measure α) : Prop where
  lebesgue_decomposition :
    ∃ p : Measure α × (α → ℝ≥0∞), Measurable p.2 ∧ p.1 ⟂ₘ ν ∧ μ = p.1 + ν.withDensity p.2
#align measure_theory.measure.have_lebesgue_decomposition MeasureTheory.Measure.HaveLebesgueDecomposition
#align measure_theory.measure.have_lebesgue_decomposition.lebesgue_decomposition MeasureTheory.Measure.HaveLebesgueDecomposition.lebesgue_decomposition

/-- If a pair of measures `HaveLebesgueDecomposition`, then `singularPart` chooses the
measure from `HaveLebesgueDecomposition`, otherwise it returns the zero measure. For sigma-finite
measures, `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`. -/
irreducible_def singularPart (μ ν : Measure α) : Measure α :=
  if h : HaveLebesgueDecomposition μ ν then (Classical.choose h.lebesgue_decomposition).1 else 0
#align measure_theory.measure.singular_part MeasureTheory.Measure.singularPart

/-- If a pair of measures `HaveLebesgueDecomposition`, then `rnDeriv` chooses the
measurable function from `HaveLebesgueDecomposition`, otherwise it returns the zero function.
For sigma-finite measures, `μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν)`.-/
irreducible_def rnDeriv (μ ν : Measure α) : α → ℝ≥0∞ :=
  if h : HaveLebesgueDecomposition μ ν then (Classical.choose h.lebesgue_decomposition).2 else 0
#align measure_theory.measure.rn_deriv MeasureTheory.Measure.rnDeriv

lemma singularPart_of_not_haveLebesgueDecomposition {μ ν : Measure α}
    (h : ¬ HaveLebesgueDecomposition μ ν) :
    μ.singularPart ν = 0 := by
  rw [singularPart]; exact dif_neg h

lemma rnDeriv_of_not_haveLebesgueDecomposition {μ ν : Measure α}
    (h : ¬ HaveLebesgueDecomposition μ ν) :
    μ.rnDeriv ν = 0 := by
  rw [rnDeriv]; exact dif_neg h

theorem haveLebesgueDecomposition_spec (μ ν : Measure α) [h : HaveLebesgueDecomposition μ ν] :
    Measurable (μ.rnDeriv ν) ∧
      μ.singularPart ν ⟂ₘ ν ∧ μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) := by
  rw [singularPart, rnDeriv, dif_pos h, dif_pos h]
  exact Classical.choose_spec h.lebesgue_decomposition
#align measure_theory.measure.have_lebesgue_decomposition_spec MeasureTheory.Measure.haveLebesgueDecomposition_spec

theorem haveLebesgueDecomposition_add (μ ν : Measure α) [HaveLebesgueDecomposition μ ν] :
    μ = μ.singularPart ν + ν.withDensity (μ.rnDeriv ν) :=
  (haveLebesgueDecomposition_spec μ ν).2.2
#align measure_theory.measure.have_lebesgue_decomposition_add MeasureTheory.Measure.haveLebesgueDecomposition_add

instance haveLebesgueDecomposition_smul (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : ℝ≥0) : (r • μ).HaveLebesgueDecomposition ν where
  lebesgue_decomposition := by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    refine' ⟨⟨r • μ.singularPart ν, r • μ.rnDeriv ν⟩, _, hsing.smul _, _⟩
    · change Measurable ((r : ℝ≥0∞) • μ.rnDeriv ν) -- cannot remove this line
      exact hmeas.const_smul _
    · change _ = (r : ℝ≥0∞) • _ + ν.withDensity ((r : ℝ≥0∞) • _)
      rw [withDensity_smul _ hmeas, ← smul_add, ← hadd]
      rfl
#align measure_theory.measure.have_lebesgue_decomposition_smul MeasureTheory.Measure.haveLebesgueDecomposition_smul

instance haveLebesgueDecomposition_smul_right (μ ν : Measure α) [HaveLebesgueDecomposition μ ν]
    (r : ℝ≥0) :
    μ.HaveLebesgueDecomposition (r • ν) where
  lebesgue_decomposition := by
    obtain ⟨hmeas, hsing, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    by_cases hr : r = 0
    · exact ⟨⟨μ, 0⟩, measurable_const, by simp [hr], by simp⟩
    refine ⟨⟨μ.singularPart ν, r⁻¹ • μ.rnDeriv ν⟩, ?_, ?_, ?_⟩
    · change Measurable (r⁻¹ • μ.rnDeriv ν)
      exact hmeas.const_smul _
    · refine MutuallySingular.mono_ac hsing AbsolutelyContinuous.rfl ?_
      exact absolutelyContinuous_of_le_smul le_rfl
    · have : r⁻¹ • rnDeriv μ ν = ((r⁻¹ : ℝ≥0) : ℝ≥0∞) • rnDeriv μ ν := by simp [ENNReal.smul_def]
      rw [this, withDensity_smul _ hmeas, ENNReal.smul_def r, withDensity_smul_measure,
        ← smul_assoc, smul_eq_mul, ENNReal.coe_inv hr, ENNReal.inv_mul_cancel, one_smul]
      · exact hadd
      · simp [hr]
      · exact ENNReal.coe_ne_top

@[measurability]
theorem measurable_rnDeriv (μ ν : Measure α) : Measurable <| μ.rnDeriv ν := by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).1
  · rw [rnDeriv, dif_neg h]
    exact measurable_zero
#align measure_theory.measure.measurable_rn_deriv MeasureTheory.Measure.measurable_rnDeriv

theorem mutuallySingular_singularPart (μ ν : Measure α) : μ.singularPart ν ⟂ₘ ν := by
  by_cases h : HaveLebesgueDecomposition μ ν
  · exact (haveLebesgueDecomposition_spec μ ν).2.1
  · rw [singularPart, dif_neg h]
    exact MutuallySingular.zero_left
#align measure_theory.measure.mutually_singular_singular_part MeasureTheory.Measure.mutuallySingular_singularPart

theorem singularPart_le (μ ν : Measure α) : μ.singularPart ν ≤ μ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · cases' (haveLebesgueDecomposition_spec μ ν).2 with _ h
    conv_rhs => rw [h]
    exact Measure.le_add_right le_rfl
  · rw [singularPart, dif_neg hl]
    exact Measure.zero_le μ
#align measure_theory.measure.singular_part_le MeasureTheory.Measure.singularPart_le

theorem withDensity_rnDeriv_le (μ ν : Measure α) : ν.withDensity (μ.rnDeriv ν) ≤ μ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · cases' (haveLebesgueDecomposition_spec μ ν).2 with _ h
    conv_rhs => rw [h]
    exact Measure.le_add_left le_rfl
  · rw [rnDeriv, dif_neg hl, withDensity_zero]
    exact Measure.zero_le μ
#align measure_theory.measure.with_density_rn_deriv_le MeasureTheory.Measure.withDensity_rnDeriv_le

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
  rw [← withDensity_rnDeriv_eq_zero,
    withDensity_eq_zero_iff (measurable_rnDeriv _ _).aemeasurable]

lemma MutuallySingular.rnDeriv_ae_eq_zero {μ ν : Measure α} (hμν : μ ⟂ₘ ν) :
    μ.rnDeriv ν =ᵐ[ν] 0 := by
  by_cases h : μ.HaveLebesgueDecomposition ν
  · rw [rnDeriv_eq_zero]
    exact hμν
  · rw [rnDeriv_of_not_haveLebesgueDecomposition h]

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

theorem lintegral_rnDeriv_lt_top_of_measure_ne_top {μ : Measure α} (ν : Measure α) {s : Set α}
    (hs : μ s ≠ ∞) : ∫⁻ x in s, μ.rnDeriv ν x ∂ν < ∞ := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · haveI := hl
    obtain ⟨-, -, hadd⟩ := haveLebesgueDecomposition_spec μ ν
    suffices : (∫⁻ x in toMeasurable μ s, μ.rnDeriv ν x ∂ν) < ∞
    exact lt_of_le_of_lt (lintegral_mono_set (subset_toMeasurable _ _)) this
    rw [← withDensity_apply _ (measurableSet_toMeasurable _ _)]
    refine'
      lt_of_le_of_lt
        (le_add_left le_rfl :
          _ ≤ μ.singularPart ν (toMeasurable μ s) + ν.withDensity (μ.rnDeriv ν) (toMeasurable μ s))
        _
    rw [← Measure.add_apply, ← hadd, measure_toMeasurable]
    exact hs.lt_top
  · erw [Measure.rnDeriv, dif_neg hl, lintegral_zero]
    exact WithTop.zero_lt_top
#align measure_theory.measure.lintegral_rn_deriv_lt_top_of_measure_ne_top MeasureTheory.Measure.lintegral_rnDeriv_lt_top_of_measure_ne_top

theorem lintegral_rnDeriv_lt_top (μ ν : Measure α) [IsFiniteMeasure μ] :
    (∫⁻ x, μ.rnDeriv ν x ∂ν) < ∞ := by
  rw [← set_lintegral_univ]
  exact lintegral_rnDeriv_lt_top_of_measure_ne_top _ (measure_lt_top _ _).ne
#align measure_theory.measure.lintegral_rn_deriv_lt_top MeasureTheory.Measure.lintegral_rnDeriv_lt_top

lemma integrable_toReal_rnDeriv {μ ν : Measure α} [IsFiniteMeasure μ] :
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
  refine' (lintegral_rnDeriv_lt_top_of_measure_ne_top _ _).ne
  exact (measure_spanningSets_lt_top _ _).ne
#align measure_theory.measure.rn_deriv_lt_top MeasureTheory.Measure.rnDeriv_lt_top

lemma rnDeriv_ne_top (μ ν : Measure α) [SigmaFinite μ] : ∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ ∞ := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx using hx.ne

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `s = μ.singularPart μ`.

This theorem provides the uniqueness of the `singularPart` in the Lebesgue decomposition theorem,
while `MeasureTheory.Measure.eq_rnDeriv` provides the uniqueness of the
`rnDeriv`. -/
theorem eq_singularPart {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : s = μ.singularPart ν := by
  haveI : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S ∩ T)ᶜ = 0 := by
    rw [compl_inter]
    refine' nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) _)
    rw [hT₃, hS₃, add_zero]
  have heq : s.restrict (S ∩ T)ᶜ = (μ.singularPart ν).restrict (S ∩ T)ᶜ := by
    ext1 A hA
    have hf : ν.withDensity f (A ∩ (S ∩ T)ᶜ) = 0 := by
      refine' withDensity_absolutelyContinuous ν _ _
      rw [← nonpos_iff_eq_zero]
      exact hνinter ▸ measure_mono (inter_subset_right _ _)
    have hrn : ν.withDensity (μ.rnDeriv ν) (A ∩ (S ∩ T)ᶜ) = 0 := by
      refine' withDensity_absolutelyContinuous ν _ _
      rw [← nonpos_iff_eq_zero]
      exact hνinter ▸ measure_mono (inter_subset_right _ _)
    rw [restrict_apply hA, restrict_apply hA, ← add_zero (s (A ∩ (S ∩ T)ᶜ)), ← hf, ← add_apply, ←
      hadd, add_apply, hrn, add_zero]
  have heq' : ∀ A : Set α, MeasurableSet A → s A = s.restrict (S ∩ T)ᶜ A := by
    intro A hA
    have hsinter : s (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hS₂ ▸ measure_mono ((inter_subset_right _ _).trans (inter_subset_left _ _))
    rw [restrict_apply hA, ← diff_eq, AEDisjoint.measure_diff_left hsinter]
  ext1 A hA
  have hμinter : μ.singularPart ν (A ∩ (S ∩ T)) = 0 := by
    rw [← nonpos_iff_eq_zero]
    exact hT₂ ▸ measure_mono ((inter_subset_right _ _).trans (inter_subset_right _ _))
  rw [heq' A hA, heq, restrict_apply hA, ← diff_eq, AEDisjoint.measure_diff_left hμinter]
#align measure_theory.measure.eq_singular_part MeasureTheory.Measure.eq_singularPart

theorem singularPart_zero (ν : Measure α) : (0 : Measure α).singularPart ν = 0 := by
  refine' (eq_singularPart measurable_zero MutuallySingular.zero_left _).symm
  rw [zero_add, withDensity_zero]
#align measure_theory.measure.singular_part_zero MeasureTheory.Measure.singularPart_zero

theorem singularPart_smul (μ ν : Measure α) (r : ℝ≥0) :
    (r • μ).singularPart ν = r • μ.singularPart ν := by
  by_cases hr : r = 0
  · rw [hr, zero_smul, zero_smul, singularPart_zero]
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine'
      (eq_singularPart ((measurable_rnDeriv μ ν).const_smul (r : ℝ≥0∞))
          (MutuallySingular.smul r (haveLebesgueDecomposition_spec _ _).2.1) _).symm
    rw [withDensity_smul _ (measurable_rnDeriv _ _), ← smul_add,
      ← haveLebesgueDecomposition_add μ ν, ENNReal.smul_def]
  · rw [singularPart, singularPart, dif_neg hl, dif_neg, smul_zero]
    refine' fun hl' => hl _
    rw [← inv_smul_smul₀ hr μ]
    exact @Measure.haveLebesgueDecomposition_smul _ _ _ _ hl' _
#align measure_theory.measure.singular_part_smul MeasureTheory.Measure.singularPart_smul

theorem singularPart_smul_right (μ ν : Measure α) (r : ℝ≥0) (hr : r ≠ 0) :
    μ.singularPart (r • ν) = μ.singularPart ν := by
  by_cases hl : HaveLebesgueDecomposition μ ν
  · refine (eq_singularPart ((measurable_rnDeriv μ ν).const_smul r⁻¹) ?_ ?_).symm
    · refine (mutuallySingular_singularPart μ ν).mono_ac AbsolutelyContinuous.rfl ?_
      exact absolutelyContinuous_of_le_smul le_rfl
    · rw [ENNReal.smul_def r, withDensity_smul_measure, ← withDensity_smul]
      swap; · exact (measurable_rnDeriv _ _).const_smul _
      convert haveLebesgueDecomposition_add μ ν
      ext x
      simp only [Pi.smul_apply, ne_eq]
      rw [← ENNReal.smul_def, ← smul_assoc, smul_eq_mul, mul_inv_cancel hr, one_smul]
  · rw [singularPart, singularPart, dif_neg hl, dif_neg]
    refine fun hl' => hl ?_
    rw [← inv_smul_smul₀ hr ν]
    infer_instance

theorem singularPart_add (μ₁ μ₂ ν : Measure α) [HaveLebesgueDecomposition μ₁ ν]
    [HaveLebesgueDecomposition μ₂ ν] :
    (μ₁ + μ₂).singularPart ν = μ₁.singularPart ν + μ₂.singularPart ν := by
  refine'
    (eq_singularPart ((measurable_rnDeriv μ₁ ν).add (measurable_rnDeriv μ₂ ν))
        ((haveLebesgueDecomposition_spec _ _).2.1.add_left
          (haveLebesgueDecomposition_spec _ _).2.1)
        _).symm
  erw [withDensity_add_left (measurable_rnDeriv μ₁ ν)]
  conv_rhs => rw [add_assoc, add_comm (μ₂.singularPart ν), ← add_assoc, ← add_assoc]
  rw [← haveLebesgueDecomposition_add μ₁ ν, add_assoc, add_comm (ν.withDensity (μ₂.rnDeriv ν)),
    ← haveLebesgueDecomposition_add μ₂ ν]
#align measure_theory.measure.singular_part_add MeasureTheory.Measure.singularPart_add

theorem singularPart_withDensity (ν : Measure α) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (ν.withDensity f).singularPart ν = 0 :=
  haveI : ν.withDensity f = 0 + ν.withDensity f := by rw [zero_add]
  (eq_singularPart hf MutuallySingular.zero_left this).symm
#align measure_theory.measure.singular_part_with_density MeasureTheory.Measure.singularPart_withDensity

/-- Given measures `μ` and `ν`, if `s` is a measure mutually singular to `ν` and `f` is a
measurable function such that `μ = s + fν`, then `f = μ.rnDeriv ν`.

This theorem provides the uniqueness of the `rnDeriv` in the Lebesgue decomposition
theorem, while `MeasureTheory.Measure.eq_singularPart` provides the uniqueness of the
`singularPart`. Here, the uniqueness is given in terms of the measures, while the uniqueness in
terms of the functions is given in `eq_rnDeriv`. -/
theorem eq_withDensity_rnDeriv {s : Measure α} {f : α → ℝ≥0∞} (hf : Measurable f) (hs : s ⟂ₘ ν)
    (hadd : μ = s + ν.withDensity f) : ν.withDensity f = ν.withDensity (μ.rnDeriv ν) := by
  haveI : HaveLebesgueDecomposition μ ν := ⟨⟨⟨s, f⟩, hf, hs, hadd⟩⟩
  obtain ⟨hmeas, hsing, hadd'⟩ := haveLebesgueDecomposition_spec μ ν
  obtain ⟨⟨S, hS₁, hS₂, hS₃⟩, ⟨T, hT₁, hT₂, hT₃⟩⟩ := hs, hsing
  rw [hadd'] at hadd
  have hνinter : ν (S ∩ T)ᶜ = 0 := by
    rw [compl_inter]
    refine' nonpos_iff_eq_zero.1 (le_trans (measure_union_le _ _) _)
    rw [hT₃, hS₃, add_zero]
  have heq :
    (ν.withDensity f).restrict (S ∩ T) = (ν.withDensity (μ.rnDeriv ν)).restrict (S ∩ T) := by
    ext1 A hA
    have hs : s (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hS₂ ▸ measure_mono ((inter_subset_right _ _).trans (inter_subset_left _ _))
    have hsing : μ.singularPart ν (A ∩ (S ∩ T)) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact hT₂ ▸ measure_mono ((inter_subset_right _ _).trans (inter_subset_right _ _))
    rw [restrict_apply hA, restrict_apply hA, ← add_zero (ν.withDensity f (A ∩ (S ∩ T))), ← hs, ←
      add_apply, add_comm, ← hadd, add_apply, hsing, zero_add]
  have heq' :
    ∀ A : Set α, MeasurableSet A → ν.withDensity f A = (ν.withDensity f).restrict (S ∩ T) A := by
    intro A hA
    have hνfinter : ν.withDensity f (A ∩ (S ∩ T)ᶜ) = 0 := by
      rw [← nonpos_iff_eq_zero]
      exact withDensity_absolutelyContinuous ν f hνinter ▸ measure_mono (inter_subset_right _ _)
    rw [restrict_apply hA, ← add_zero (ν.withDensity f (A ∩ (S ∩ T))), ← hνfinter, ← diff_eq,
      measure_inter_add_diff _ (hS₁.inter hT₁)]
  ext1 A hA
  have hνrn : ν.withDensity (μ.rnDeriv ν) (A ∩ (S ∩ T)ᶜ) = 0 := by
    rw [← nonpos_iff_eq_zero]
    exact
      withDensity_absolutelyContinuous ν (μ.rnDeriv ν) hνinter ▸
        measure_mono (inter_subset_right _ _)
  rw [heq' A hA, heq, ← add_zero ((ν.withDensity (μ.rnDeriv ν)).restrict (S ∩ T) A), ← hνrn,
    restrict_apply hA, ← diff_eq, measure_inter_add_diff _ (hS₁.inter hT₁)]
#align measure_theory.measure.eq_with_density_rn_deriv MeasureTheory.Measure.eq_withDensity_rnDeriv

theorem eq_withDensity_rnDeriv₀ {μ ν : Measure α} {s : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) :
    ν.withDensity f = ν.withDensity (μ.rnDeriv ν) := by
  rw [withDensity_congr_ae hf.ae_eq_mk] at hadd ⊢
  exact eq_withDensity_rnDeriv hf.measurable_mk hs hadd

theorem eq_rnDeriv₀ {μ ν : Measure α} [SigmaFinite ν] {s : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hs : s ⟂ₘ ν) (hadd : μ = s + ν.withDensity f) :
    f =ᵐ[ν] μ.rnDeriv ν := by
  refine' ae_eq_of_forall_set_lintegral_eq_of_sigmaFinite₀ hf
    (measurable_rnDeriv μ ν).aemeasurable _
  intro a ha _
  calc ∫⁻ x : α in a, f x ∂ν = ν.withDensity f a := (withDensity_apply f ha).symm
    _ = ν.withDensity (μ.rnDeriv ν) a := by rw [eq_withDensity_rnDeriv₀ hf hs hadd]
    _ = ∫⁻ x : α in a, μ.rnDeriv ν x ∂ν := withDensity_apply _ ha

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
theorem rnDeriv_withDensity (ν : Measure α) [SigmaFinite ν] {f : α → ℝ≥0∞} (hf : Measurable f) :
    (ν.withDensity f).rnDeriv ν =ᵐ[ν] f :=
  haveI : ν.withDensity f = 0 + ν.withDensity f := by rw [zero_add]
  (eq_rnDeriv hf MutuallySingular.zero_left this).symm
#align measure_theory.measure.rn_deriv_with_density MeasureTheory.Measure.rnDeriv_withDensity

/-- The Radon-Nikodym derivative of the restriction of a measure to a measurable set is the
indicator function of this set. -/
theorem rnDeriv_restrict (ν : Measure α) [SigmaFinite ν] {s : Set α} (hs : MeasurableSet s) :
    (ν.restrict s).rnDeriv ν =ᵐ[ν] s.indicator 1 := by
  rw [← withDensity_indicator_one hs]
  exact rnDeriv_withDensity _ (measurable_one.indicator hs)
#align measure_theory.measure.rn_deriv_restrict MeasureTheory.Measure.rnDeriv_restrict

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
  suffices ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ by
    suffices hμ : μ ≪ r • μ by exact hμ.ae_le this
    refine absolutelyContinuous_of_le_smul (c := r⁻¹) ?_
    rw [← ENNReal.coe_inv hr, ← ENNReal.smul_def, ← smul_assoc, smul_eq_mul,
      inv_mul_cancel hr, one_smul]
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
  have hAmeas : MeasurableSet A := MeasurableSet.iInter fun n => (hf₁ n).compl
  have hA₂ : ∀ n : ℕ, μ.toSignedMeasure - ((1 / (n + 1) : ℝ≥0) • ν).toSignedMeasure ≤[A] 0 := by
    intro n; exact restrict_le_restrict_subset _ _ (hf₁ n).compl (hf₃ n) (iInter_subset _ _)
  have hA₃ : ∀ n : ℕ, μ A ≤ (1 / (n + 1) : ℝ≥0) * ν A := by
    intro n
    have := nonpos_of_restrict_le_zero _ (hA₂ n)
    rwa [toSignedMeasure_sub_apply hAmeas, sub_nonpos, ENNReal.toReal_le_toReal] at this
    exacts [ne_of_lt (measure_lt_top _ _), ne_of_lt (measure_lt_top _ _)]
  have hμ : μ A = 0 := by
    lift μ A to ℝ≥0 using ne_of_lt (measure_lt_top _ _) with μA
    lift ν A to ℝ≥0 using ne_of_lt (measure_lt_top _ _) with νA
    rw [ENNReal.coe_eq_zero]
    by_cases hb : 0 < νA
    · suffices ∀ b, 0 < b → μA ≤ b by
        by_contra h
        have h' := this (μA / 2) (half_pos (zero_lt_iff.2 h))
        rw [← @Classical.not_not (μA ≤ μA / 2)] at h'
        exact h' (not_le.2 (NNReal.half_lt_self h))
      intro c hc
      have : ∃ n : ℕ, 1 / (n + 1 : ℝ) < c * (νA : ℝ)⁻¹; refine' exists_nat_one_div_lt _
      · refine' mul_pos hc _
        rw [_root_.inv_pos]; exact hb
      rcases this with ⟨n, hn⟩
      have hb₁ : (0 : ℝ) < (νA : ℝ)⁻¹ := by rw [_root_.inv_pos]; exact hb
      have h' : 1 / (↑n + 1) * νA < c := by
        rw [← NNReal.coe_lt_coe, ← mul_lt_mul_right hb₁, NNReal.coe_mul, mul_assoc, ←
          NNReal.coe_inv, ← NNReal.coe_mul, _root_.mul_inv_cancel, ← NNReal.coe_mul, mul_one,
          NNReal.coe_inv]
        · exact hn
        · exact Ne.symm (ne_of_lt hb)
      refine' le_trans _ (le_of_lt h')
      rw [← ENNReal.coe_le_coe, ENNReal.coe_mul]
      exact hA₃ n
    · rw [not_lt, le_zero_iff] at hb
      specialize hA₃ 0
      simp [hb, le_zero_iff] at hA₃
      assumption
  -- since `μ` and `ν` are not mutually singular, `μ A = 0` implies `ν Aᶜ > 0`
  rw [MutuallySingular] at h; push_neg at h
  have := h _ hAmeas hμ
  simp_rw [compl_iInter, compl_compl] at this
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
  ⟨measurable_zero, fun A _ => by simp⟩
#align measure_theory.measure.lebesgue_decomposition.zero_mem_measurable_le MeasureTheory.Measure.LebesgueDecomposition.zero_mem_measurableLE

theorem sup_mem_measurableLE {f g : α → ℝ≥0∞} (hf : f ∈ measurableLE μ ν)
    (hg : g ∈ measurableLE μ ν) : (fun a => f a ⊔ g a) ∈ measurableLE μ ν := by
  simp_rw [ENNReal.sup_eq_max]
  refine' ⟨Measurable.max hf.1 hg.1, fun A hA => _⟩
  have h₁ := hA.inter (measurableSet_le hf.1 hg.1)
  have h₂ := hA.inter (measurableSet_lt hg.1 hf.1)
  rw [set_lintegral_max hf.1 hg.1]
  refine' (add_le_add (hg.2 _ h₁) (hf.2 _ h₂)).trans_eq _
  · simp only [← not_le, ← compl_setOf, ← diff_eq]
    exact measure_inter_add_diff _ (measurableSet_le hf.1 hg.1)
#align measure_theory.measure.lebesgue_decomposition.sup_mem_measurable_le MeasureTheory.Measure.LebesgueDecomposition.sup_mem_measurableLE

theorem iSup_succ_eq_sup {α} (f : ℕ → α → ℝ≥0∞) (m : ℕ) (a : α) :
    ⨆ (k : ℕ) (_ : k ≤ m + 1), f k a = f m.succ a ⊔ ⨆ (k : ℕ) (_ : k ≤ m), f k a := by
  refine Option.ext fun x => ?_
  simp only [Option.mem_def, ENNReal.some_eq_coe]
  constructor <;> intro h <;> rw [← h]; symm
  all_goals
    set c := ⨆ (k : ℕ) (_ : k ≤ m + 1), f k a with hc
    set d := f m.succ a ⊔ ⨆ (k : ℕ) (_ : k ≤ m), f k a with hd
    rw [@le_antisymm_iff ℝ≥0∞, hc, hd]
    -- Specifying the type is weirdly necessary
    refine' ⟨_, _⟩
    · refine' iSup₂_le fun n hn => _
      rcases Nat.of_le_succ hn with (h | h)
      · exact le_sup_of_le_right (le_iSup₂ (f := fun k (_ : k ≤ m) => f k a) n h)
      · exact h ▸ le_sup_left
    · refine' sup_le _ (biSup_mono fun n hn => hn.trans m.le_succ)
      convert @le_iSup₂ ℝ≥0∞ ℕ (fun i => i ≤ m + 1) _ _ m.succ le_rfl
      rfl
#align measure_theory.measure.lebesgue_decomposition.supr_succ_eq_sup MeasureTheory.Measure.LebesgueDecomposition.iSup_succ_eq_sup

theorem iSup_mem_measurableLE (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurableLE μ ν) (n : ℕ) :
    (fun x => ⨆ (k) (_ : k ≤ n), f k x) ∈ measurableLE μ ν := by
  induction' n with m hm
  · refine' ⟨_, _⟩
    · simp [(hf 0).1]
    · intro A hA; simp [(hf 0).2 A hA]
  · have :
      (fun a : α => ⨆ (k : ℕ) (_ : k ≤ m + 1), f k a) = fun a =>
        f m.succ a ⊔ ⨆ (k : ℕ) (_ : k ≤ m), f k a :=
      funext fun _ => iSup_succ_eq_sup _ _ _
    refine' ⟨measurable_iSup fun n => Measurable.iSup_Prop _ (hf n).1, fun A hA => _⟩
    rw [this]; exact (sup_mem_measurableLE (hf m.succ) hm).2 A hA
#align measure_theory.measure.lebesgue_decomposition.supr_mem_measurable_le MeasureTheory.Measure.LebesgueDecomposition.iSup_mem_measurableLE

theorem iSup_mem_measurableLE' (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, f n ∈ measurableLE μ ν) (n : ℕ) :
    (⨆ (k) (_ : k ≤ n), f k) ∈ measurableLE μ ν := by
  convert iSup_mem_measurableLE f hf n
  refine Option.ext fun x => ?_; simp
#align measure_theory.measure.lebesgue_decomposition.supr_mem_measurable_le' MeasureTheory.Measure.LebesgueDecomposition.iSup_mem_measurableLE'

section SuprLemmas

--TODO: these statements should be moved elsewhere

theorem iSup_monotone {α : Type*} (f : ℕ → α → ℝ≥0∞) :
    Monotone fun n x => ⨆ (k) (_ : k ≤ n), f k x := fun _ _ hnm _ =>
  biSup_mono fun _ => ge_trans hnm
#align measure_theory.measure.lebesgue_decomposition.supr_monotone MeasureTheory.Measure.LebesgueDecomposition.iSup_monotone

theorem iSup_monotone' {α : Type*} (f : ℕ → α → ℝ≥0∞) (x : α) :
    Monotone fun n => ⨆ (k) (_ : k ≤ n), f k x := fun _ _ hnm => iSup_monotone f hnm x
#align measure_theory.measure.lebesgue_decomposition.supr_monotone' MeasureTheory.Measure.LebesgueDecomposition.iSup_monotone'

theorem iSup_le_le {α : Type*} (f : ℕ → α → ℝ≥0∞) (n k : ℕ) (hk : k ≤ n) :
    f k ≤ fun x => ⨆ (k) (_ : k ≤ n), f k x :=
  fun x => le_iSup₂ (f := fun k (_ : k ≤ n) => f k x) k hk
#align measure_theory.measure.lebesgue_decomposition.supr_le_le MeasureTheory.Measure.LebesgueDecomposition.iSup_le_le

end SuprLemmas

/-- `measurableLEEval μ ν` is the set of `∫⁻ x, f x ∂μ` for all `f ∈ measurableLE μ ν`. -/
def measurableLEEval (μ ν : Measure α) : Set ℝ≥0∞ :=
  (fun f : α → ℝ≥0∞ => ∫⁻ x, f x ∂μ) '' measurableLE μ ν
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
    have h :=
      @exists_seq_tendsto_sSup _ _ _ _ _ (measurableLEEval ν μ)
        ⟨0, 0, zero_mem_measurableLE, by simp⟩ (OrderTop.bddAbove _)
    choose g _ hg₂ f hf₁ hf₂ using h
    -- we set `ξ` to be the supremum of an increasing sequence of functions obtained from above
    set ξ := ⨆ (n) (k) (_ : k ≤ n), f k with hξ
    -- we see that `ξ` has the largest integral among all functions in `measurableLE`
    have hξ₁ : sSup (measurableLEEval ν μ) = ∫⁻ a, ξ a ∂ν := by
      have :=
        @lintegral_tendsto_of_tendsto_of_monotone _ _ ν (fun n => ⨆ (k) (_ : k ≤ n), f k)
          (⨆ (n) (k) (_ : k ≤ n), f k) ?_ ?_ ?_
      · refine' tendsto_nhds_unique _ this
        refine' tendsto_of_tendsto_of_tendsto_of_le_of_le hg₂ tendsto_const_nhds _ _
        · intro n; rw [← hf₂ n]
          apply lintegral_mono
          simp only [iSup_apply, iSup_le_le f n n le_rfl]
        · intro n
          exact le_sSup ⟨⨆ (k : ℕ) (_ : k ≤ n), f k, iSup_mem_measurableLE' _ hf₁ _, rfl⟩
      · intro n
        refine' Measurable.aemeasurable _
        convert (iSup_mem_measurableLE _ hf₁ n).1
        refine Option.ext fun x => ?_; simp
      · refine' Filter.eventually_of_forall fun a => _
        simp [iSup_monotone' f _]
      · refine' Filter.eventually_of_forall fun a => _
        simp [tendsto_atTop_iSup (iSup_monotone' f a)]
    have hξm : Measurable ξ := by
      convert measurable_iSup fun n => (iSup_mem_measurableLE _ hf₁ n).1
      refine Option.ext fun x => ?_; simp [hξ]
    -- `ξ` is the `f` in the theorem statement and we set `μ₁` to be `μ - ν.withDensity ξ`
    -- since we need `μ₁ + ν.withDensity ξ = μ`
    set μ₁ := μ - ν.withDensity ξ with hμ₁
    have hle : ν.withDensity ξ ≤ μ := by
      intro B hB
      rw [hξ, withDensity_apply _ hB]
      simp_rw [iSup_apply]
      rw [lintegral_iSup (fun i => (iSup_mem_measurableLE _ hf₁ i).1) (iSup_monotone _)]
      exact iSup_le fun i => (iSup_mem_measurableLE _ hf₁ i).2 B hB
    have : IsFiniteMeasure (ν.withDensity ξ) := by
      refine' isFiniteMeasure_withDensity _
      have hle' := hle univ MeasurableSet.univ
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hle'
      exact ne_top_of_le_ne_top (measure_ne_top _ _) hle'
    refine' ⟨⟨μ₁, ξ⟩, hξm, _, _⟩
    · by_contra h
      -- if they are not mutually singular, then from `exists_positive_of_not_mutuallySingular`,
      -- there exists some `ε > 0` and a measurable set `E`, such that `μ(E) > 0` and `E` is
      -- positive with respect to `ν - εμ`
      obtain ⟨ε, hε₁, E, hE₁, hE₂, hE₃⟩ := exists_positive_of_not_mutuallySingular μ₁ ν h
      simp_rw [hμ₁] at hE₃
      have hξle : ∀ A, MeasurableSet A → (∫⁻ a in A, ξ a ∂ν) ≤ μ A := by
        intro A hA; rw [hξ]
        simp_rw [iSup_apply]
        rw [lintegral_iSup (fun n => (iSup_mem_measurableLE _ hf₁ n).1) (iSup_monotone _)]
        exact iSup_le fun n => (iSup_mem_measurableLE _ hf₁ n).2 A hA
      -- since `E` is positive, we have `∫⁻ a in A ∩ E, ε + ξ a ∂ν ≤ μ (A ∩ E)` for all `A`
      have hε₂ : ∀ A : Set α, MeasurableSet A → (∫⁻ a in A ∩ E, ε + ξ a ∂ν) ≤ μ (A ∩ E) := by
        intro A hA
        have := subset_le_of_restrict_le_restrict _ _ hE₁ hE₃ (inter_subset_right A E)
        rwa [zero_apply, toSignedMeasure_sub_apply (hA.inter hE₁),
          Measure.sub_apply (hA.inter hE₁) hle,
          ENNReal.toReal_sub_of_le _ (ne_of_lt (measure_lt_top _ _)), sub_nonneg, le_sub_iff_add_le,
          ← ENNReal.toReal_add, ENNReal.toReal_le_toReal, Measure.coe_smul, Pi.smul_apply,
          withDensity_apply _ (hA.inter hE₁), show ε • ν (A ∩ E) = (ε : ℝ≥0∞) * ν (A ∩ E) by rfl,
          ← set_lintegral_const, ← lintegral_add_left measurable_const] at this
        · rw [Ne.def, ENNReal.add_eq_top, not_or]
          exact ⟨ne_of_lt (measure_lt_top _ _), ne_of_lt (measure_lt_top _ _)⟩
        · exact ne_of_lt (measure_lt_top _ _)
        · exact ne_of_lt (measure_lt_top _ _)
        · exact ne_of_lt (measure_lt_top _ _)
        · rw [withDensity_apply _ (hA.inter hE₁)]
          exact hξle (A ∩ E) (hA.inter hE₁)
      -- from this, we can show `ξ + ε * E.indicator` is a function in `measurableLE` with
      -- integral greater than `ξ`
      have hξε : (ξ + E.indicator fun _ => (ε : ℝ≥0∞)) ∈ measurableLE ν μ := by
        refine' ⟨Measurable.add hξm (Measurable.indicator measurable_const hE₁), fun A hA => _⟩
        have :
          (∫⁻ a in A, (ξ + E.indicator fun _ => (ε : ℝ≥0∞)) a ∂ν) =
            (∫⁻ a in A ∩ E, ε + ξ a ∂ν) + ∫⁻ a in A \ E, ξ a ∂ν := by
          simp only [lintegral_add_left measurable_const, lintegral_add_left hξm,
            set_lintegral_const, add_assoc, lintegral_inter_add_diff _ _ hE₁, Pi.add_apply,
            lintegral_indicator _ hE₁, restrict_apply hE₁]
          rw [inter_comm, add_comm]
        rw [this, ← measure_inter_add_diff A hE₁]
        exact add_le_add (hε₂ A hA) (hξle (A \ E) (hA.diff hE₁))
      have : (∫⁻ a, ξ a + E.indicator (fun _ => (ε : ℝ≥0∞)) a ∂ν) ≤ sSup (measurableLEEval ν μ) :=
        le_sSup ⟨ξ + E.indicator fun _ => (ε : ℝ≥0∞), hξε, rfl⟩
      -- but this contradicts the maximality of `∫⁻ x, ξ x ∂ν`
      refine' not_lt.2 this _
      rw [hξ₁, lintegral_add_left hξm, lintegral_indicator _ hE₁, set_lintegral_const]
      refine' ENNReal.lt_add_right _ (ENNReal.mul_pos_iff.2 ⟨ENNReal.coe_pos.2 hε₁, hE₂⟩).ne'
      have := measure_ne_top (ν.withDensity ξ) univ
      rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
    -- since `ν.withDensity ξ ≤ μ`, it is clear that `μ = μ₁ + ν.withDensity ξ`
    · rw [hμ₁]; ext1 A hA
      rw [Measure.coe_add, Pi.add_apply, Measure.sub_apply hA hle, add_comm,
        add_tsub_cancel_of_le (hle A hA)]⟩
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
    set μn : ℕ → Measure α := fun n => μ.restrict (S.set n) with hμn
    have hμ : μ = sum μn := by rw [hμn, ← restrict_iUnion h₂ S.set_mem, S.spanning, restrict_univ]
    set νn : ℕ → Measure α := fun n => ν.restrict (T.set n) with hνn
    have hν : ν = sum νn := by rw [hνn, ← restrict_iUnion h₃ T.set_mem, T.spanning, restrict_univ]
    -- As `S` is finite with respect to both `μ` and `ν`, it is clear that `μn n` and `νn n` are
    -- finite measures for all `n : ℕ`. Thus, we may apply the finite Lebesgue decomposition theorem
    -- to `μn n` and `νn n`. We define `ξ` as the sum of the singular part of the Lebesgue
    -- decompositions of `μn n` and `νn n`, and `f` as the sum of the Radon-Nikodym derivatives of
    -- `μn n` and `νn n` restricted on `S n`
    set ξ := sum fun n => singularPart (μn n) (νn n) with hξ
    set f := ∑' n, (S.set n).indicator (rnDeriv (μn n) (νn n))
    -- I claim `ξ` and `f` form a Lebesgue decomposition of `μ` and `ν`
    refine' ⟨⟨ξ, f⟩, _, _, _⟩
    · exact
        Measurable.ennreal_tsum' fun n =>
          Measurable.indicator (measurable_rnDeriv (μn n) (νn n)) (S.set_mem n)
    -- We show that `ξ` is mutually singular with respect to `ν`
    · choose A hA₁ hA₂ hA₃ using fun n => mutuallySingular_singularPart (μn n) (νn n)
      simp only [hξ]
      -- We use the set `B := ⋃ j, (S.set j) ∩ A j` where `A n` is the set provided as
      -- `singularPart (μn n) (νn n) ⟂ₘ νn n`
      refine' ⟨⋃ j, S.set j ∩ A j, MeasurableSet.iUnion fun n => (S.set_mem n).inter (hA₁ n), _, _⟩
      -- `ξ B = 0` since `ξ B = ∑ i j, singularPart (μn j) (νn j) (S.set i ∩ A i)`
      --                     `= ∑ i, singularPart (μn i) (νn i) (S.set i ∩ A i)`
      --                     `≤ ∑ i, singularPart (μn i) (νn i) (A i) = 0`
      -- where the second equality follows as `singularPart (μn j) (νn j) (S.set i ∩ A i)` vanishes
      -- for all `i ≠ j`
      · rw [measure_iUnion]
        · have :
            ∀ i,
              (sum fun n => (μn n).singularPart (νn n)) (S.set i ∩ A i) =
                (μn i).singularPart (νn i) (S.set i ∩ A i) := by
            intro i; rw [sum_apply _ ((S.set_mem i).inter (hA₁ i)), tsum_eq_single i]
            · intro j hij
              rw [hμn, ← nonpos_iff_eq_zero]
              refine' le_trans ((singularPart_le _ _) _ ((S.set_mem i).inter (hA₁ i))) (le_of_eq _)
              rw [restrict_apply ((S.set_mem i).inter (hA₁ i)), inter_comm, ← inter_assoc]
              have : Disjoint (S.set j) (S.set i) := h₂ hij
              rw [disjoint_iff_inter_eq_empty] at this
              rw [this, empty_inter, measure_empty]
          simp_rw [this, tsum_eq_zero_iff ENNReal.summable]
          intro n; exact measure_mono_null (inter_subset_right _ _) (hA₂ n)
        · exact h₂.mono fun i j => Disjoint.mono inf_le_left inf_le_left
        · exact fun n => (S.set_mem n).inter (hA₁ n)
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
        · exact h₂.mono fun i j => Disjoint.mono inf_le_left inf_le_left
        · exact fun n => (S.set_mem n).inter (hA₁ n).compl
    -- Finally, it remains to show `μ = ξ + ν.withDensity f`. Since `μ = sum μn`, and
    -- `ξ + ν.withDensity f = ∑ n, singularPart (μn n) (νn n)`
    --                        `+ ν.withDensity (rnDeriv (μn n) (νn n)) ∩ (S.set n)`,
    -- it suffices to show that the individual summands are equal. This follows by the
    -- Lebesgue decomposition properties on the individual `μn n` and `νn n`
    · simp only
      nth_rw 1 [hμ]
      rw [withDensity_tsum _, sum_add_sum]
      · refine' sum_congr fun n => _
        nth_rw 1 [haveLebesgueDecomposition_add (μn n) (νn n)]
        suffices heq :
          (νn n).withDensity ((μn n).rnDeriv (νn n)) =
            ν.withDensity ((S.set n).indicator ((μn n).rnDeriv (νn n)))
        · rw [heq]
        rw [hν, withDensity_indicator (S.set_mem n), restrict_sum _ (S.set_mem n)]
        suffices hsumeq : (sum fun i : ℕ => (νn i).restrict (S.set n)) = νn n
        · rw [hsumeq]
        ext1 s hs
        rw [sum_apply _ hs, tsum_eq_single n, hνn, h₁, restrict_restrict (T.set_mem n), inter_self]
        · intro m hm
          rw [hνn, h₁, restrict_restrict (T.set_mem n), (h₃ hm.symm).inter_eq, restrict_empty,
            coe_zero, Pi.zero_apply]
      · exact fun n => Measurable.indicator (measurable_rnDeriv _ _) (S.set_mem n)⟩
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
  suffices ν.rnDeriv (r • μ) =ᵐ[r • μ] r⁻¹ • ν.rnDeriv μ by
    suffices hμ : μ ≪ r • μ by exact hμ.ae_le this
    refine absolutelyContinuous_of_le_smul (c := r⁻¹) ?_
    rw [← ENNReal.coe_inv hr, ← ENNReal.smul_def, ← smul_assoc, smul_eq_mul,
      inv_mul_cancel hr, one_smul]
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
  have : (r.toNNReal)⁻¹ • rnDeriv ν μ = r⁻¹ • rnDeriv ν μ := by
    ext x
    simp only [Pi.smul_apply, ENNReal.smul_def, ne_eq, smul_eq_mul]
    rw [ENNReal.coe_inv, ENNReal.coe_toNNReal hr_ne_top]
    rw [ne_eq, ENNReal.toNNReal_eq_zero_iff]
    simp [hr, hr_ne_top]
  simp_rw [this, ENNReal.smul_def, ENNReal.coe_toNNReal hr_ne_top] at h
  exact h

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

end rnDeriv

end Measure

namespace SignedMeasure

open Measure

/-- A signed measure `s` is said to `HaveLebesgueDecomposition` with respect to a measure `μ`
if the positive part and the negative part of `s` both `HaveLebesgueDecomposition` with
respect to `μ`. -/
class HaveLebesgueDecomposition (s : SignedMeasure α) (μ : Measure α) : Prop where
  posPart : s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ
  negPart : s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ
#align measure_theory.signed_measure.have_lebesgue_decomposition MeasureTheory.SignedMeasure.HaveLebesgueDecomposition
#align measure_theory.signed_measure.have_lebesgue_decomposition.pos_part MeasureTheory.SignedMeasure.HaveLebesgueDecomposition.posPart
#align measure_theory.signed_measure.have_lebesgue_decomposition.neg_part MeasureTheory.SignedMeasure.HaveLebesgueDecomposition.negPart

attribute [instance] HaveLebesgueDecomposition.posPart

attribute [instance] HaveLebesgueDecomposition.negPart

theorem not_haveLebesgueDecomposition_iff (s : SignedMeasure α) (μ : Measure α) :
    ¬s.HaveLebesgueDecomposition μ ↔
      ¬s.toJordanDecomposition.posPart.HaveLebesgueDecomposition μ ∨
        ¬s.toJordanDecomposition.negPart.HaveLebesgueDecomposition μ :=
  ⟨fun h => not_or_of_imp fun hp hn => h ⟨hp, hn⟩, fun h hl => (not_and_or.2 h) ⟨hl.1, hl.2⟩⟩
#align measure_theory.signed_measure.not_have_lebesgue_decomposition_iff MeasureTheory.SignedMeasure.not_haveLebesgueDecomposition_iff

-- `infer_instance` directly does not work
-- see Note [lower instance priority]
instance (priority := 100) haveLebesgueDecomposition_of_sigmaFinite (s : SignedMeasure α)
    (μ : Measure α) [SigmaFinite μ] : s.HaveLebesgueDecomposition μ where
  posPart := inferInstance
  negPart := inferInstance
#align measure_theory.signed_measure.have_lebesgue_decomposition_of_sigma_finite MeasureTheory.SignedMeasure.haveLebesgueDecomposition_of_sigmaFinite

instance haveLebesgueDecomposition_neg (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] : (-s).HaveLebesgueDecomposition μ where
  posPart := by
    rw [toJordanDecomposition_neg, JordanDecomposition.neg_posPart]
    infer_instance
  negPart := by
    rw [toJordanDecomposition_neg, JordanDecomposition.neg_negPart]
    infer_instance
#align measure_theory.signed_measure.have_lebesgue_decomposition_neg MeasureTheory.SignedMeasure.haveLebesgueDecomposition_neg

instance haveLebesgueDecomposition_smul (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] (r : ℝ≥0) : (r • s).HaveLebesgueDecomposition μ where
  posPart := by
    rw [toJordanDecomposition_smul, JordanDecomposition.smul_posPart]
    infer_instance
  negPart := by
    rw [toJordanDecomposition_smul, JordanDecomposition.smul_negPart]
    infer_instance
#align measure_theory.signed_measure.have_lebesgue_decomposition_smul MeasureTheory.SignedMeasure.haveLebesgueDecomposition_smul

instance haveLebesgueDecomposition_smul_real (s : SignedMeasure α) (μ : Measure α)
    [s.HaveLebesgueDecomposition μ] (r : ℝ) : (r • s).HaveLebesgueDecomposition μ := by
  by_cases hr : 0 ≤ r
  · lift r to ℝ≥0 using hr
    exact s.haveLebesgueDecomposition_smul μ _
  · rw [not_le] at hr
    refine'
      { posPart := by
          rw [toJordanDecomposition_smul_real, JordanDecomposition.real_smul_posPart_neg _ _ hr]
          infer_instance
        negPart := by
          rw [toJordanDecomposition_smul_real, JordanDecomposition.real_smul_negPart_neg _ _ hr]
          infer_instance }
#align measure_theory.signed_measure.have_lebesgue_decomposition_smul_real MeasureTheory.SignedMeasure.haveLebesgueDecomposition_smul_real

/-- Given a signed measure `s` and a measure `μ`, `s.singularPart μ` is the signed measure
such that `s.singularPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s` and
`s.singularPart μ` is mutually singular with respect to `μ`. -/
def singularPart (s : SignedMeasure α) (μ : Measure α) : SignedMeasure α :=
  (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure -
    (s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure
#align measure_theory.signed_measure.singular_part MeasureTheory.SignedMeasure.singularPart

section

theorem singularPart_mutuallySingular (s : SignedMeasure α) (μ : Measure α) :
    s.toJordanDecomposition.posPart.singularPart μ ⟂ₘ
      s.toJordanDecomposition.negPart.singularPart μ := by
  by_cases hl : s.HaveLebesgueDecomposition μ
  · haveI := hl
    obtain ⟨i, hi, hpos, hneg⟩ := s.toJordanDecomposition.mutuallySingular
    rw [s.toJordanDecomposition.posPart.haveLebesgueDecomposition_add μ] at hpos
    rw [s.toJordanDecomposition.negPart.haveLebesgueDecomposition_add μ] at hneg
    rw [add_apply, add_eq_zero_iff] at hpos hneg
    exact ⟨i, hi, hpos.1, hneg.1⟩
  · rw [not_haveLebesgueDecomposition_iff] at hl
    cases' hl with hp hn
    · rw [Measure.singularPart, dif_neg hp]
      exact MutuallySingular.zero_left
    · rw [Measure.singularPart, Measure.singularPart, dif_neg hn]
      exact MutuallySingular.zero_right
#align measure_theory.signed_measure.singular_part_mutually_singular MeasureTheory.SignedMeasure.singularPart_mutuallySingular

theorem singularPart_totalVariation (s : SignedMeasure α) (μ : Measure α) :
    (s.singularPart μ).totalVariation =
      s.toJordanDecomposition.posPart.singularPart μ +
        s.toJordanDecomposition.negPart.singularPart μ := by
  have :
    (s.singularPart μ).toJordanDecomposition =
      ⟨s.toJordanDecomposition.posPart.singularPart μ,
        s.toJordanDecomposition.negPart.singularPart μ, singularPart_mutuallySingular s μ⟩ := by
    refine' JordanDecomposition.toSignedMeasure_injective _
    rw [toSignedMeasure_toJordanDecomposition]
    rfl
  · rw [totalVariation, this]
#align measure_theory.signed_measure.singular_part_total_variation MeasureTheory.SignedMeasure.singularPart_totalVariation

nonrec theorem mutuallySingular_singularPart (s : SignedMeasure α) (μ : Measure α) :
    singularPart s μ ⟂ᵥ μ.toENNRealVectorMeasure := by
  rw [mutuallySingular_ennreal_iff, singularPart_totalVariation]
  change _ ⟂ₘ VectorMeasure.equivMeasure.toFun (VectorMeasure.equivMeasure.invFun μ)
  rw [VectorMeasure.equivMeasure.right_inv μ]
  exact (mutuallySingular_singularPart _ _).add_left (mutuallySingular_singularPart _ _)
#align measure_theory.signed_measure.mutually_singular_singular_part MeasureTheory.SignedMeasure.mutuallySingular_singularPart

end

/-- The Radon-Nikodym derivative between a signed measure and a positive measure.

`rnDeriv s μ` satisfies `μ.withDensityᵥ (s.rnDeriv μ) = s`
if and only if `s` is absolutely continuous with respect to `μ` and this fact is known as
`MeasureTheory.SignedMeasure.absolutelyContinuous_iff_withDensity_rnDeriv_eq`
and can be found in `MeasureTheory.Decomposition.RadonNikodym`. -/
def rnDeriv (s : SignedMeasure α) (μ : Measure α) : α → ℝ := fun x =>
  (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal -
    (s.toJordanDecomposition.negPart.rnDeriv μ x).toReal
#align measure_theory.signed_measure.rn_deriv MeasureTheory.SignedMeasure.rnDeriv

-- Porting note: The generated equation theorem is the form of `rnDeriv s μ x`.

theorem rnDeriv_def (s : SignedMeasure α) (μ : Measure α) : rnDeriv s μ = fun x =>
    (s.toJordanDecomposition.posPart.rnDeriv μ x).toReal -
      (s.toJordanDecomposition.negPart.rnDeriv μ x).toReal :=
  rfl

attribute [eqns rnDeriv_def] rnDeriv

variable {s t : SignedMeasure α}

@[measurability]
theorem measurable_rnDeriv (s : SignedMeasure α) (μ : Measure α) : Measurable (rnDeriv s μ) := by
  rw [rnDeriv]
  measurability
#align measure_theory.signed_measure.measurable_rn_deriv MeasureTheory.SignedMeasure.measurable_rnDeriv

theorem integrable_rnDeriv (s : SignedMeasure α) (μ : Measure α) : Integrable (rnDeriv s μ) μ := by
  refine' Integrable.sub _ _ <;>
    · constructor
      · apply Measurable.aestronglyMeasurable; measurability
      exact hasFiniteIntegral_toReal_of_lintegral_ne_top (lintegral_rnDeriv_lt_top _ μ).ne
#align measure_theory.signed_measure.integrable_rn_deriv MeasureTheory.SignedMeasure.integrable_rnDeriv

variable (s μ)

/-- **The Lebesgue Decomposition theorem between a signed measure and a measure**:
Given a signed measure `s` and a σ-finite measure `μ`, there exist a signed measure `t` and a
measurable and integrable function `f`, such that `t` is mutually singular with respect to `μ`
and `s = t + μ.with_densityᵥ f`. In this case `t = s.singular_part μ` and
`f = s.rn_deriv μ`. -/
theorem singularPart_add_withDensity_rnDeriv_eq [s.HaveLebesgueDecomposition μ] :
    s.singularPart μ + μ.withDensityᵥ (s.rnDeriv μ) = s := by
  conv_rhs =>
    rw [← toSignedMeasure_toJordanDecomposition s, JordanDecomposition.toSignedMeasure]
  rw [singularPart, rnDeriv,
    withDensityᵥ_sub' (integrable_toReal_of_lintegral_ne_top _ _)
      (integrable_toReal_of_lintegral_ne_top _ _),
    withDensityᵥ_toReal, withDensityᵥ_toReal, sub_eq_add_neg, sub_eq_add_neg,
    add_comm (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure, ← add_assoc,
    add_assoc (-(s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure),
    ← toSignedMeasure_add, add_comm, ← add_assoc, ← neg_add, ← toSignedMeasure_add, add_comm,
    ← sub_eq_add_neg]
  convert rfl
  -- `convert rfl` much faster than `congr`
  · exact s.toJordanDecomposition.posPart.haveLebesgueDecomposition_add μ
  · rw [add_comm]
    exact s.toJordanDecomposition.negPart.haveLebesgueDecomposition_add μ
  all_goals
    first
    | exact (lintegral_rnDeriv_lt_top _ _).ne
    | measurability
#align measure_theory.signed_measure.singular_part_add_with_density_rn_deriv_eq MeasureTheory.SignedMeasure.singularPart_add_withDensity_rnDeriv_eq

variable {s μ}

theorem jordanDecomposition_add_withDensity_mutuallySingular {f : α → ℝ} (hf : Measurable f)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) :
    (t.toJordanDecomposition.posPart + μ.withDensity fun x : α => ENNReal.ofReal (f x)) ⟂ₘ
      t.toJordanDecomposition.negPart + μ.withDensity fun x : α => ENNReal.ofReal (-f x) := by
  rw [mutuallySingular_ennreal_iff, totalVariation_mutuallySingular_iff] at htμ
  change
    _ ⟂ₘ VectorMeasure.equivMeasure.toFun (VectorMeasure.equivMeasure.invFun μ) ∧
      _ ⟂ₘ VectorMeasure.equivMeasure.toFun (VectorMeasure.equivMeasure.invFun μ) at htμ
  rw [VectorMeasure.equivMeasure.right_inv] at htμ
  exact
    ((JordanDecomposition.mutuallySingular _).add_right
          (htμ.1.mono_ac (refl _) (withDensity_absolutelyContinuous _ _))).add_left
      ((htμ.2.symm.mono_ac (withDensity_absolutelyContinuous _ _) (refl _)).add_right
        (withDensity_ofReal_mutuallySingular hf))
#align measure_theory.signed_measure.jordan_decomposition_add_with_density_mutually_singular MeasureTheory.SignedMeasure.jordanDecomposition_add_withDensity_mutuallySingular

theorem toJordanDecomposition_eq_of_eq_add_withDensity {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.toJordanDecomposition =
      @JordanDecomposition.mk α _
        (t.toJordanDecomposition.posPart + μ.withDensity fun x => ENNReal.ofReal (f x))
        (t.toJordanDecomposition.negPart + μ.withDensity fun x => ENNReal.ofReal (-f x))
        (by haveI := isFiniteMeasure_withDensity_ofReal hfi.2; infer_instance)
        (by haveI := isFiniteMeasure_withDensity_ofReal hfi.neg.2; infer_instance)
        (jordanDecomposition_add_withDensity_mutuallySingular hf htμ) := by
  haveI := isFiniteMeasure_withDensity_ofReal hfi.2
  haveI := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  refine' toJordanDecomposition_eq _
  simp_rw [JordanDecomposition.toSignedMeasure, hadd]
  ext i hi
  rw [VectorMeasure.sub_apply, toSignedMeasure_apply_measurable hi,
      toSignedMeasure_apply_measurable hi, add_apply, add_apply, ENNReal.toReal_add,
      ENNReal.toReal_add, add_sub_add_comm, ← toSignedMeasure_apply_measurable hi,
      ← toSignedMeasure_apply_measurable hi, ← VectorMeasure.sub_apply,
      ← JordanDecomposition.toSignedMeasure, toSignedMeasure_toJordanDecomposition,
      VectorMeasure.add_apply, ← toSignedMeasure_apply_measurable hi,
      ← toSignedMeasure_apply_measurable hi,
      withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hfi,
      VectorMeasure.sub_apply] <;>
    exact (measure_lt_top _ _).ne
#align measure_theory.signed_measure.to_jordan_decomposition_eq_of_eq_add_with_density MeasureTheory.SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity

private theorem haveLebesgueDecomposition_mk' (μ : Measure α) {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.HaveLebesgueDecomposition μ := by
  have htμ' := htμ
  rw [mutuallySingular_ennreal_iff] at htμ
  change _ ⟂ₘ VectorMeasure.equivMeasure.toFun (VectorMeasure.equivMeasure.invFun μ) at htμ
  rw [VectorMeasure.equivMeasure.right_inv, totalVariation_mutuallySingular_iff] at htμ
  refine'
    { posPart := by
        use ⟨t.toJordanDecomposition.posPart, fun x => ENNReal.ofReal (f x)⟩
        refine' ⟨hf.ennreal_ofReal, htμ.1, _⟩
        rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd]
      negPart := by
        use ⟨t.toJordanDecomposition.negPart, fun x => ENNReal.ofReal (-f x)⟩
        refine' ⟨hf.neg.ennreal_ofReal, htμ.2, _⟩
        rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd] }

theorem haveLebesgueDecomposition_mk (μ : Measure α) {f : α → ℝ} (hf : Measurable f)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    s.HaveLebesgueDecomposition μ := by
  by_cases hfi : Integrable f μ
  · exact haveLebesgueDecomposition_mk' μ hf hfi htμ hadd
  · rw [withDensityᵥ, dif_neg hfi, add_zero] at hadd
    refine' haveLebesgueDecomposition_mk' μ measurable_zero (integrable_zero _ _ μ) htμ _
    rwa [withDensityᵥ_zero, add_zero]
#align measure_theory.signed_measure.have_lebesgue_decomposition_mk MeasureTheory.SignedMeasure.haveLebesgueDecomposition_mk

private theorem eq_singularPart' (t : SignedMeasure α) {f : α → ℝ} (hf : Measurable f)
    (hfi : Integrable f μ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    t = s.singularPart μ := by
  have htμ' := htμ
  rw [mutuallySingular_ennreal_iff, totalVariation_mutuallySingular_iff] at htμ
  change
    _ ⟂ₘ VectorMeasure.equivMeasure.toFun (VectorMeasure.equivMeasure.invFun μ) ∧
      _ ⟂ₘ VectorMeasure.equivMeasure.toFun (VectorMeasure.equivMeasure.invFun μ) at htμ
  rw [VectorMeasure.equivMeasure.right_inv] at htμ
  · rw [singularPart, ← t.toSignedMeasure_toJordanDecomposition,
      JordanDecomposition.toSignedMeasure]
    congr
    · have hfpos : Measurable fun x => ENNReal.ofReal (f x) := by measurability
      refine' eq_singularPart hfpos htμ.1 _
      rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd]
    · have hfneg : Measurable fun x => ENNReal.ofReal (-f x) := by measurability
      refine' eq_singularPart hfneg htμ.2 _
      rw [toJordanDecomposition_eq_of_eq_add_withDensity hf hfi htμ' hadd]

/-- Given a measure `μ`, signed measures `s` and `t`, and a function `f` such that `t` is
mutually singular with respect to `μ` and `s = t + μ.withDensityᵥ f`, we have
`t = singularPart s μ`, i.e. `t` is the singular part of the Lebesgue decomposition between
`s` and `μ`. -/
theorem eq_singularPart (t : SignedMeasure α) (f : α → ℝ) (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure)
    (hadd : s = t + μ.withDensityᵥ f) : t = s.singularPart μ := by
  by_cases hfi : Integrable f μ
  · refine' eq_singularPart' t hfi.1.measurable_mk (hfi.congr hfi.1.ae_eq_mk) htμ _
    convert hadd using 2
    exact WithDensityᵥEq.congr_ae hfi.1.ae_eq_mk.symm
  · rw [withDensityᵥ, dif_neg hfi, add_zero] at hadd
    refine' eq_singularPart' t measurable_zero (integrable_zero _ _ μ) htμ _
    rwa [withDensityᵥ_zero, add_zero]
#align measure_theory.signed_measure.eq_singular_part MeasureTheory.SignedMeasure.eq_singularPart

theorem singularPart_zero (μ : Measure α) : (0 : SignedMeasure α).singularPart μ = 0 := by
  refine' (eq_singularPart 0 0 VectorMeasure.MutuallySingular.zero_left _).symm
  rw [zero_add, withDensityᵥ_zero]
#align measure_theory.signed_measure.singular_part_zero MeasureTheory.SignedMeasure.singularPart_zero

theorem singularPart_neg (s : SignedMeasure α) (μ : Measure α) :
    (-s).singularPart μ = -s.singularPart μ := by
  have h₁ :
    ((-s).toJordanDecomposition.posPart.singularPart μ).toSignedMeasure =
      (s.toJordanDecomposition.negPart.singularPart μ).toSignedMeasure := by
    refine' toSignedMeasure_congr _
    rw [toJordanDecomposition_neg, JordanDecomposition.neg_posPart]
  have h₂ :
    ((-s).toJordanDecomposition.negPart.singularPart μ).toSignedMeasure =
      (s.toJordanDecomposition.posPart.singularPart μ).toSignedMeasure := by
    refine' toSignedMeasure_congr _
    rw [toJordanDecomposition_neg, JordanDecomposition.neg_negPart]
  rw [singularPart, singularPart, neg_sub, h₁, h₂]
#align measure_theory.signed_measure.singular_part_neg MeasureTheory.SignedMeasure.singularPart_neg

theorem singularPart_smul_nnreal (s : SignedMeasure α) (μ : Measure α) (r : ℝ≥0) :
    (r • s).singularPart μ = r • s.singularPart μ := by
  rw [singularPart, singularPart, smul_sub, ← toSignedMeasure_smul, ← toSignedMeasure_smul]
  conv_lhs =>
    congr
    · congr
      · rw [toJordanDecomposition_smul, JordanDecomposition.smul_posPart, singularPart_smul]
    · congr
      rw [toJordanDecomposition_smul, JordanDecomposition.smul_negPart, singularPart_smul]
#align measure_theory.signed_measure.singular_part_smul_nnreal MeasureTheory.SignedMeasure.singularPart_smul_nnreal

nonrec theorem singularPart_smul (s : SignedMeasure α) (μ : Measure α) (r : ℝ) :
    (r • s).singularPart μ = r • s.singularPart μ := by
  by_cases hr : 0 ≤ r
  · lift r to ℝ≥0 using hr
    exact singularPart_smul_nnreal s μ r
  · rw [singularPart, singularPart]
    conv_lhs =>
      congr
      · congr
        · rw [toJordanDecomposition_smul_real,
            JordanDecomposition.real_smul_posPart_neg _ _ (not_le.1 hr), singularPart_smul]
      · congr
        · rw [toJordanDecomposition_smul_real,
            JordanDecomposition.real_smul_negPart_neg _ _ (not_le.1 hr), singularPart_smul]
    rw [toSignedMeasure_smul, toSignedMeasure_smul, ← neg_sub, ← smul_sub]
    change -(((-r).toNNReal : ℝ) • (_ : SignedMeasure α)) = _
    rw [← neg_smul, Real.coe_toNNReal _ (le_of_lt (neg_pos.mpr (not_le.1 hr))), neg_neg]
#align measure_theory.signed_measure.singular_part_smul MeasureTheory.SignedMeasure.singularPart_smul

theorem singularPart_add (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] :
    (s + t).singularPart μ = s.singularPart μ + t.singularPart μ := by
  refine'
    (eq_singularPart _ (s.rnDeriv μ + t.rnDeriv μ)
        ((mutuallySingular_singularPart s μ).add_left (mutuallySingular_singularPart t μ))
        _).symm
  erw [withDensityᵥ_add (integrable_rnDeriv s μ) (integrable_rnDeriv t μ)]
  rw [add_assoc, add_comm (t.singularPart μ), add_assoc, add_comm _ (t.singularPart μ),
    singularPart_add_withDensity_rnDeriv_eq, ← add_assoc,
    singularPart_add_withDensity_rnDeriv_eq]
#align measure_theory.signed_measure.singular_part_add MeasureTheory.SignedMeasure.singularPart_add

theorem singularPart_sub (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] :
    (s - t).singularPart μ = s.singularPart μ - t.singularPart μ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, singularPart_add, singularPart_neg]
#align measure_theory.signed_measure.singular_part_sub MeasureTheory.SignedMeasure.singularPart_sub

/-- Given a measure `μ`, signed measures `s` and `t`, and a function `f` such that `t` is
mutually singular with respect to `μ` and `s = t + μ.withDensityᵥ f`, we have
`f = rnDeriv s μ`, i.e. `f` is the Radon-Nikodym derivative of `s` and `μ`. -/
theorem eq_rnDeriv (t : SignedMeasure α) (f : α → ℝ) (hfi : Integrable f μ)
    (htμ : t ⟂ᵥ μ.toENNRealVectorMeasure) (hadd : s = t + μ.withDensityᵥ f) :
    f =ᵐ[μ] s.rnDeriv μ := by
  set f' := hfi.1.mk f
  have hadd' : s = t + μ.withDensityᵥ f' := by
    convert hadd using 2
    exact WithDensityᵥEq.congr_ae hfi.1.ae_eq_mk.symm
  haveI := haveLebesgueDecomposition_mk μ hfi.1.measurable_mk htμ hadd'
  refine' (Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _) hfi _).symm
  rw [← add_right_inj t, ← hadd, eq_singularPart _ f htμ hadd,
    singularPart_add_withDensity_rnDeriv_eq]
#align measure_theory.signed_measure.eq_rn_deriv MeasureTheory.SignedMeasure.eq_rnDeriv

theorem rnDeriv_neg (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] :
    (-s).rnDeriv μ =ᵐ[μ] -s.rnDeriv μ := by
  refine'
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _) (integrable_rnDeriv _ _).neg _
  rw [withDensityᵥ_neg, ← add_right_inj ((-s).singularPart μ),
    singularPart_add_withDensity_rnDeriv_eq, singularPart_neg, ← neg_add,
    singularPart_add_withDensity_rnDeriv_eq]
#align measure_theory.signed_measure.rn_deriv_neg MeasureTheory.SignedMeasure.rnDeriv_neg

theorem rnDeriv_smul (s : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ] (r : ℝ) :
    (r • s).rnDeriv μ =ᵐ[μ] r • s.rnDeriv μ := by
  refine'
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _)
      ((integrable_rnDeriv _ _).smul r) _
  change _ = μ.withDensityᵥ ((r : ℝ) • s.rnDeriv μ)
  rw [withDensityᵥ_smul (rnDeriv s μ) (r : ℝ), ← add_right_inj ((r • s).singularPart μ),
    singularPart_add_withDensity_rnDeriv_eq, singularPart_smul]
  change _ = _ + r • _
  rw [← smul_add, singularPart_add_withDensity_rnDeriv_eq]
#align measure_theory.signed_measure.rn_deriv_smul MeasureTheory.SignedMeasure.rnDeriv_smul

theorem rnDeriv_add (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] [(s + t).HaveLebesgueDecomposition μ] :
    (s + t).rnDeriv μ =ᵐ[μ] s.rnDeriv μ + t.rnDeriv μ := by
  refine'
    Integrable.ae_eq_of_withDensityᵥ_eq (integrable_rnDeriv _ _)
      ((integrable_rnDeriv _ _).add (integrable_rnDeriv _ _)) _
  rw [← add_right_inj ((s + t).singularPart μ), singularPart_add_withDensity_rnDeriv_eq,
    withDensityᵥ_add (integrable_rnDeriv _ _) (integrable_rnDeriv _ _), singularPart_add,
    add_assoc, add_comm (t.singularPart μ), add_assoc, add_comm _ (t.singularPart μ),
    singularPart_add_withDensity_rnDeriv_eq, ← add_assoc,
    singularPart_add_withDensity_rnDeriv_eq]
#align measure_theory.signed_measure.rn_deriv_add MeasureTheory.SignedMeasure.rnDeriv_add

theorem rnDeriv_sub (s t : SignedMeasure α) (μ : Measure α) [s.HaveLebesgueDecomposition μ]
    [t.HaveLebesgueDecomposition μ] [hst : (s - t).HaveLebesgueDecomposition μ] :
    (s - t).rnDeriv μ =ᵐ[μ] s.rnDeriv μ - t.rnDeriv μ := by
  rw [sub_eq_add_neg] at hst
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact ae_eq_trans (rnDeriv_add _ _ _) (Filter.EventuallyEq.add (ae_eq_refl _) (rnDeriv_neg _ _))
#align measure_theory.signed_measure.rn_deriv_sub MeasureTheory.SignedMeasure.rnDeriv_sub

end SignedMeasure

namespace ComplexMeasure

/-- A complex measure is said to `HaveLebesgueDecomposition` with respect to a positive measure
if both its real and imaginary part `HaveLebesgueDecomposition` with respect to that measure. -/
class HaveLebesgueDecomposition (c : ComplexMeasure α) (μ : Measure α) : Prop where
  rePart : c.re.HaveLebesgueDecomposition μ
  imPart : c.im.HaveLebesgueDecomposition μ
#align measure_theory.complex_measure.have_lebesgue_decomposition MeasureTheory.ComplexMeasure.HaveLebesgueDecomposition
#align measure_theory.complex_measure.have_lebesgue_decomposition.re_part MeasureTheory.ComplexMeasure.HaveLebesgueDecomposition.rePart
#align measure_theory.complex_measure.have_lebesgue_decomposition.im_part MeasureTheory.ComplexMeasure.HaveLebesgueDecomposition.imPart

attribute [instance] HaveLebesgueDecomposition.rePart

attribute [instance] HaveLebesgueDecomposition.imPart

/-- The singular part between a complex measure `c` and a positive measure `μ` is the complex
measure satisfying `c.singularPart μ + μ.withDensityᵥ (c.rnDeriv μ) = c`. This property is given
by `MeasureTheory.ComplexMeasure.singularPart_add_withDensity_rnDeriv_eq`. -/
def singularPart (c : ComplexMeasure α) (μ : Measure α) : ComplexMeasure α :=
  (c.re.singularPart μ).toComplexMeasure (c.im.singularPart μ)
#align measure_theory.complex_measure.singular_part MeasureTheory.ComplexMeasure.singularPart

/-- The Radon-Nikodym derivative between a complex measure and a positive measure. -/
def rnDeriv (c : ComplexMeasure α) (μ : Measure α) : α → ℂ := fun x =>
  ⟨c.re.rnDeriv μ x, c.im.rnDeriv μ x⟩
#align measure_theory.complex_measure.rn_deriv MeasureTheory.ComplexMeasure.rnDeriv

variable {c : ComplexMeasure α}

theorem integrable_rnDeriv (c : ComplexMeasure α) (μ : Measure α) : Integrable (c.rnDeriv μ) μ := by
  rw [← memℒp_one_iff_integrable, ← memℒp_re_im_iff]
  exact
    ⟨memℒp_one_iff_integrable.2 (SignedMeasure.integrable_rnDeriv _ _),
      memℒp_one_iff_integrable.2 (SignedMeasure.integrable_rnDeriv _ _)⟩
#align measure_theory.complex_measure.integrable_rn_deriv MeasureTheory.ComplexMeasure.integrable_rnDeriv

theorem singularPart_add_withDensity_rnDeriv_eq [c.HaveLebesgueDecomposition μ] :
    c.singularPart μ + μ.withDensityᵥ (c.rnDeriv μ) = c := by
  conv_rhs => rw [← c.toComplexMeasure_to_signedMeasure]
  ext i hi : 1
  rw [VectorMeasure.add_apply, SignedMeasure.toComplexMeasure_apply]
  ext
  · rw [Complex.add_re, withDensityᵥ_apply (c.integrable_rnDeriv μ) hi, ← IsROrC.re_eq_complex_re,
      ← integral_re (c.integrable_rnDeriv μ).integrableOn, IsROrC.re_eq_complex_re,
      ← withDensityᵥ_apply _ hi]
    · change (c.re.singularPart μ + μ.withDensityᵥ (c.re.rnDeriv μ)) i = _
      rw [c.re.singularPart_add_withDensity_rnDeriv_eq μ]
    · exact SignedMeasure.integrable_rnDeriv _ _
  · rw [Complex.add_im, withDensityᵥ_apply (c.integrable_rnDeriv μ) hi, ← IsROrC.im_eq_complex_im,
      ← integral_im (c.integrable_rnDeriv μ).integrableOn, IsROrC.im_eq_complex_im,
      ← withDensityᵥ_apply _ hi]
    · change (c.im.singularPart μ + μ.withDensityᵥ (c.im.rnDeriv μ)) i = _
      rw [c.im.singularPart_add_withDensity_rnDeriv_eq μ]
    · exact SignedMeasure.integrable_rnDeriv _ _
#align measure_theory.complex_measure.singular_part_add_with_density_rn_deriv_eq MeasureTheory.ComplexMeasure.singularPart_add_withDensity_rnDeriv_eq

end ComplexMeasure

end MeasureTheory
