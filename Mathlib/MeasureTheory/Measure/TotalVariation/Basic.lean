/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.MeasureTheory.Measure.MutuallySingular
public import Mathlib.MeasureTheory.Measure.TotalVariation.Defs
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.Set

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

variable {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
  {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

lemma tvDist_of_mutuallySingular (hμν : μ ⟂ₘ ν) :
    tvDist μ ν = μ.real Set.univ + ν.real Set.univ := by
  rw [add_comm, ← tvDist_restrict_add_compl hμν.measurableSet_nullSet]
  simp

lemma tvDist_eq_of_isHahnDecomposition {s : Set 𝓧} (h : IsHahnDecomposition μ ν s) :
    tvDist μ ν = ν.real s - μ.real s + (μ.real sᶜ - ν.real sᶜ) := by
  rw [← tvDist_restrict_add_compl h.measurableSet, tvDist_of_le h.le_on, tvDist_of_ge h.ge_on_compl]
  simp

lemma tvDist_withDensity_self_eq_integral {f : 𝓧 → ℝ≥0∞} (hf : Measurable f)
    (hf_top : ∀ᵐ x ∂μ, f x ≠ ∞)
    [IsFiniteMeasure (μ.withDensity f)] :
    tvDist (μ.withDensity f) μ = ∫ x, |1 - (f x).toReal| ∂μ := by
  have h_hahn : IsHahnDecomposition (μ.withDensity f) μ {x | f x ≤ 1} :=
    IsHahnDecomposition_withDensity_le_one hf
  rw [tvDist_eq_of_isHahnDecomposition h_hahn]
  unfold Measure.real
  rw [withDensity_apply _ (measurableSet_le hf measurable_const),
    withDensity_apply _ (measurableSet_le hf measurable_const).compl]
  rw [← integral_toReal (by fun_prop), ← integral_toReal (by fun_prop)]
  rotate_left
  · exact ae_restrict_of_ae <| by filter_upwards [hf_top] with x hx using hx.lt_top
  · exact ae_restrict_of_ae <| by filter_upwards [hf_top] with x hx using hx.lt_top
  have hf_int : Integrable (fun x ↦ (f x).toReal) μ := by
    rw [integrable_toReal_iff (by fun_prop) hf_top, ← setLIntegral_univ,
      ← withDensity_apply _ .univ]
    exact measure_ne_top _ _
  have h1 : μ.real {x | f x ≤ 1} - ∫ x in {x | f x ≤ 1}, (f x).toReal ∂μ =
      ∫ x in {x | f x ≤ 1}, 1 - (f x).toReal ∂μ := by
    rw [← setIntegral_one_eq_measureReal, ← integral_sub (by simp) hf_int.integrableOn]
  have h2 : ∫ x in {x | f x ≤ 1}ᶜ, (f x).toReal ∂μ - μ.real {x | f x ≤ 1}ᶜ =
      ∫ x in {x | f x ≤ 1}ᶜ, (f x).toReal - 1 ∂μ := by
    rw [← setIntegral_one_eq_measureReal, ← integral_sub hf_int.integrableOn (by simp)]
  rw [← Measure.real, ← Measure.real, h1, h2]
  calc ∫ x in {x | f x ≤ 1}, 1 - (f x).toReal ∂μ + ∫ x in {x | f x ≤ 1}ᶜ, (f x).toReal - 1 ∂μ
  _ = ∫ x in {x | f x ≤ 1}, |1 - (f x).toReal| ∂μ +
      ∫ x in {x | f x ≤ 1}ᶜ,|1 - (f x).toReal| ∂μ := by
    congr 1
    · refine setIntegral_congr_fun (measurableSet_le hf measurable_const) fun x hx ↦ ?_
      rw [abs_of_nonneg]
      simp only [Set.mem_setOf_eq, sub_nonneg] at hx ⊢
      exact ENNReal.toReal_le_of_le_ofReal (by simp) (by simp [hx])
    · refine setIntegral_congr_ae (measurableSet_le hf measurable_const).compl ?_
      filter_upwards [hf_top] with x hx_top hx
      rw [abs_of_nonpos]
      · simp
      · simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hx
        simp only [tsub_le_iff_right, zero_add]
        rw [← ENNReal.toReal_one]
        gcongr
  _ = ∫ x, |1 - (f x).toReal| ∂μ := by
    refine integral_add_compl (measurableSet_le hf measurable_const) ?_
    exact (Integrable.sub (by simp) hf_int).abs

lemma tvDist_eq_integral_abs_rnDeriv_of_ac (hμν : μ ≪ ν) :
    tvDist μ ν = ∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν := by
  have : tvDist μ ν = tvDist (ν.withDensity (μ.rnDeriv ν)) ν := by
    congr
    rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
  rw [this, tvDist_withDensity_self_eq_integral (by fun_prop) (Measure.rnDeriv_ne_top μ ν)]

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

theorem tvDist_eq_integral_abs_rnDeriv_add_singularPart :
    tvDist μ ν = ∫ x, |1 - (μ.rnDeriv ν x).toReal| ∂ν + (μ.singularPart ν).real Set.univ := by
  have : tvDist μ ν = tvDist (ν.withDensity (μ.rnDeriv ν) + μ.singularPart ν) ν := by
    simp_rw [Measure.rnDeriv_add_singularPart μ ν]
  rw [this, tvDist_add_of_ac_of_mutuallySingular
    (withDensity_absolutelyContinuous ν (μ.rnDeriv ν)) (μ.mutuallySingular_singularPart ν),
    tvDist_withDensity_self_eq_integral (by fun_prop) (μ.rnDeriv_ne_top ν)]

end MeasureTheory
