/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs

import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Properties of the total variation distance

We prove properties of the total variation distance, in particular alternative formulas for it.

## Main statements

* `tvDist_eq_integral_abs_rnDeriv_add_singularPart`: the total variation distance satisfies the
  formula `tvDist μ ν = ∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν + (μ.singularPart ν).real Set.univ`.

-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧} {μ ν : Measure 𝓧}

lemma etvDist_of_mutuallySingular (hμν : μ ⟂ₘ ν) :
    etvDist μ ν = μ Set.univ + ν Set.univ := by
  rw [add_comm, ← etvDist_restrict_add_compl hμν.measurableSet_nullSet]
  simp

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

lemma tvDist_of_mutuallySingular (hμν : μ ⟂ₘ ν) :
    tvDist μ ν = μ.real Set.univ + ν.real Set.univ := by
  rw [add_comm, ← tvDist_restrict_add_compl hμν.measurableSet_nullSet]
  simp

lemma IsHahnDecomposition.etvDist_eq {s : Set 𝓧} (h : IsHahnDecomposition μ ν s) :
    etvDist μ ν = ν s - μ s + (μ sᶜ - ν sᶜ) := by
  rw [← etvDist_restrict_add_compl h.measurableSet, etvDist_of_le h.le_on,
    etvDist_of_ge h.ge_on_compl]
  simp

lemma IsHahnDecomposition.tvDist_eq {s : Set 𝓧} (h : IsHahnDecomposition μ ν s) :
    tvDist μ ν = ν.real s - μ.real s + (μ.real sᶜ - ν.real sᶜ) := by
  rw [← tvDist_restrict_add_compl h.measurableSet, tvDist_of_le h.le_on, tvDist_of_ge h.ge_on_compl]
  simp

lemma tvDist_withDensity_self_eq_integral {f : 𝓧 → ℝ≥0∞} (hf : Integrable f μ) :
    tvDist (μ.withDensity f) μ = ∫ x, |1 - (f x).toReal| ∂μ := by
  have hf_meas : AEMeasurable f μ := hf.aemeasurable
  have hf_lintegral : ∫⁻ x, f x ∂μ ≠ ∞ := hf.hasFiniteIntegral.ne
  have : IsFiniteMeasure (μ.withDensity f) := isFiniteMeasure_withDensity hf_lintegral
  have hf_top : ∀ᵐ x ∂μ, f x ≠ ∞ := by
    filter_upwards [ae_lt_top' hf_meas hf_lintegral] with x hx using hx.ne
  obtain ⟨s, hs, hs_le, hs_ge⟩ : ∃ s, MeasurableSet s ∧ (∀ᵐ x ∂μ.restrict s, f x ≤ 1) ∧
      ∀ᵐ x ∂μ.restrict sᶜ, 1 ≤ f x := by
    have hs : MeasurableSet {x | hf_meas.mk f x ≤ 1} :=
      measurableSet_le hf_meas.measurable_mk measurable_const
    refine ⟨{x | hf_meas.mk f x ≤ 1}, hs, ?_, ?_⟩
    · filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae hf_meas.ae_eq_mk] with x hxs hx
      rwa [hx]
    · filter_upwards [ae_restrict_mem hs.compl, ae_restrict_of_ae hf_meas.ae_eq_mk] with x hxs hx
      grind
  have h_hahn : IsHahnDecomposition (μ.withDensity f) μ s :=
    isHahnDecomposition_withDensity_of_ae_le_one hs hs_le hs_ge
  rw [h_hahn.tvDist_eq,
    withDensity_real_apply_eq_integral hf_meas.restrict ?_ hs.nullMeasurableSet,
    withDensity_real_apply_eq_integral hf_meas.restrict ?_ hs.compl.nullMeasurableSet]
  rotate_left
  · filter_upwards [hf_top] with x hx _ using hx.lt_top
  · filter_upwards [hf_top] with x hx _ using hx.lt_top
  have hf_toReal : Integrable (fun x ↦ (f x).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hf_meas hf_lintegral
  have h1 : μ.real s - ∫ x in s, (f x).toReal ∂μ = ∫ x in s, 1 - (f x).toReal ∂μ := by
    rw [← setIntegral_one_eq_measureReal, ← integral_sub (by simp) hf_toReal.integrableOn]
  have h2 : ∫ x in sᶜ, (f x).toReal ∂μ - μ.real sᶜ = ∫ x in sᶜ, (f x).toReal - 1 ∂μ := by
    rw [← setIntegral_one_eq_measureReal, ← integral_sub hf_toReal.integrableOn (by simp)]
  rw [h1, h2]
  calc ∫ x in s, 1 - (f x).toReal ∂μ + ∫ x in sᶜ, (f x).toReal - 1 ∂μ
  _ = ∫ x in s, |1 - (f x).toReal| ∂μ + ∫ x in sᶜ, |1 - (f x).toReal| ∂μ := by
    congr 1
    · refine integral_congr_ae ?_
      filter_upwards [hs_le] with x hx
      rw [abs_of_nonneg]
      simp only [sub_nonneg]
      exact ENNReal.toReal_le_of_le_ofReal (by simp) (by simp [hx])
    · refine integral_congr_ae ?_
      filter_upwards [hs_ge, ae_restrict_of_ae hf_top] with x hx hx_top
      rw [abs_of_nonpos]
      · simp
      · simp only [tsub_le_iff_right, zero_add]
        rw [← ENNReal.toReal_one]
        gcongr
  _ = ∫ x, |1 - (f x).toReal| ∂μ := by
    refine integral_add_compl hs ?_
    exact (Integrable.sub (by simp) hf_toReal).abs

lemma etvDist_withDensity_self_eq_lintegral {f : 𝓧 → ℝ≥0∞} (hf : Integrable f μ) :
    etvDist (μ.withDensity f) μ = ∫⁻ x, ‖1 - (f x).toReal‖ₑ ∂μ := by
  have hf_lintegral : ∫⁻ x, f x ∂μ ≠ ∞ := hf.hasFiniteIntegral.ne
  have : IsFiniteMeasure (μ.withDensity f) := isFiniteMeasure_withDensity hf_lintegral
  rw [← ofReal_tvDist, tvDist_withDensity_self_eq_integral hf,
    ofReal_integral_eq_lintegral_ofReal]
  · congr with x
    rw [← Real.norm_eq_abs, ofReal_norm]
  · refine (Integrable.sub (by simp) ?_).abs
    exact integrable_toReal_of_lintegral_ne_top hf.aemeasurable hf_lintegral
  · filter_upwards with
    positivity

lemma tvDist_eq_integral_abs_rnDeriv_of_ac (hμν : μ ≪ ν) :
    tvDist μ ν = ∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν := by
  conv_lhs => rw! [← μ.withDensity_rnDeriv_eq ν hμν,
    tvDist_withDensity_self_eq_integral Measure.integrable_rnDeriv]

lemma etvDist_eq_lintegral_enorm_rnDeriv_of_ac (hμν : μ ≪ ν) :
    etvDist μ ν = ∫⁻ x, ‖1 - (μ.rnDeriv ν x).toReal‖ₑ ∂ν := by
  conv_lhs => rw! [← μ.withDensity_rnDeriv_eq ν hμν,
    etvDist_withDensity_self_eq_lintegral Measure.integrable_rnDeriv]

lemma tvDist_add_of_ac_of_mutuallySingular {μ' : Measure 𝓧} [IsFiniteMeasure μ']
    (hμν : μ ≪ ν) (hμ'ν : μ' ⟂ₘ ν) :
    tvDist (μ + μ') ν = tvDist μ ν + μ'.real Set.univ := by
  rw [← tvDist_restrict_add_compl hμ'ν.measurableSet_nullSet]
  simp only [Measure.restrict_add, hμ'ν.restrict_nullSet, add_zero, hμ'ν.restrict_nullSet',
    hμ'ν.restrict_compl_nullSet', hμ'ν.restrict_compl_nullSet, tvDist_zero_right]
  have hμ_eq_zero : μ.restrict hμ'ν.nullSetᶜ = 0 := by
    simp only [Measure.restrict_eq_zero]
    exact hμν (by simp)
  have hμ_eq : μ.restrict hμ'ν.nullSet = μ := by
    conv_rhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hμ'ν.measurableSet_nullSet]
    simp [hμ_eq_zero]
  simp [hμ_eq, hμ_eq_zero]

lemma etvDist_add_of_ac_of_mutuallySingular {μ' : Measure 𝓧} [IsFiniteMeasure μ']
    (hμν : μ ≪ ν) (hμ'ν : μ' ⟂ₘ ν) :
    etvDist (μ + μ') ν = etvDist μ ν + μ' Set.univ := by
  rw [← ofReal_tvDist, tvDist_add_of_ac_of_mutuallySingular hμν hμ'ν,
    ENNReal.ofReal_add tvDist_nonneg (by simp), ofReal_tvDist, ofReal_measureReal]

theorem tvDist_eq_integral_abs_rnDeriv_add_singularPart :
    tvDist μ ν = ∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν + (μ.singularPart ν).real Set.univ := by
  have : tvDist μ ν = tvDist (ν.withDensity (μ.rnDeriv ν) + μ.singularPart ν) ν := by
    simp_rw [Measure.rnDeriv_add_singularPart μ ν]
  rw [this, tvDist_add_of_ac_of_mutuallySingular
    (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) (μ.mutuallySingular_singularPart ν),
    tvDist_withDensity_self_eq_integral Measure.integrable_rnDeriv]

theorem etvDist_eq_lintegral_enorm_rnDeriv_add_singularPart :
    etvDist μ ν = ∫⁻ x, ‖1 - (μ.rnDeriv ν x).toReal‖ₑ ∂ν + μ.singularPart ν Set.univ := by
  rw [← ofReal_tvDist, tvDist_eq_integral_abs_rnDeriv_add_singularPart,
    ENNReal.ofReal_add (by positivity) (by simp), ofReal_measureReal,
    ofReal_integral_eq_lintegral_ofReal]
  · congr with x
    rw [← Real.norm_eq_abs, ofReal_norm]
  · refine (Integrable.sub (by simp) ?_).abs
    exact Measure.integrable_toReal_rnDeriv
  · filter_upwards with
    positivity

end MeasureTheory
