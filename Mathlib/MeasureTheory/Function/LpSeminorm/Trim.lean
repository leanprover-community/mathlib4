/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

#align_import measure_theory.function.lp_seminorm from "leanprover-community/mathlib"@"c4015acc0a223449d44061e27ddac1835a3852b9"

/-!
# Lp seminorm with respect to trimmed measure

In this file we prove basic properties of the Lp-seminorm of a function
with respect to the restriction of a measure to a sub-σ-algebra.
-/

namespace MeasureTheory

open Filter
open scoped ENNReal

variable {α E : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ : Measure α}
  [NormedAddCommGroup E]

theorem snorm'_trim (hm : m ≤ m0) {f : α → E} (hf : StronglyMeasurable[m] f) :
    snorm' f q (μ.trim hm) = snorm' f q μ := by
  simp_rw [snorm']
  congr 1
  refine lintegral_trim hm ?_
  refine @Measurable.pow_const _ _ _ _ _ _ _ m _ (@Measurable.coe_nnreal_ennreal _ m _ ?_) q
  apply @StronglyMeasurable.measurable
  exact @StronglyMeasurable.nnnorm α m _ _ _ hf
#align measure_theory.snorm'_trim MeasureTheory.snorm'_trim

theorem limsup_trim (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : Measurable[m] f) :
    limsup f (ae (μ.trim hm)) = limsup f (ae μ) := by
  simp_rw [limsup_eq]
  suffices h_set_eq : { a : ℝ≥0∞ | ∀ᵐ n ∂μ.trim hm, f n ≤ a } = { a : ℝ≥0∞ | ∀ᵐ n ∂μ, f n ≤ a } by
    rw [h_set_eq]
  ext1 a
  suffices h_meas_eq : μ { x | ¬f x ≤ a } = μ.trim hm { x | ¬f x ≤ a } by
    simp_rw [Set.mem_setOf_eq, ae_iff, h_meas_eq]
  refine (trim_measurableSet_eq hm ?_).symm
  refine @MeasurableSet.compl _ _ m (@measurableSet_le ℝ≥0∞ _ _ _ _ m _ _ _ _ _ hf ?_)
  exact @measurable_const _ _ _ m _
#align measure_theory.limsup_trim MeasureTheory.limsup_trim

theorem essSup_trim (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : Measurable[m] f) :
    essSup f (μ.trim hm) = essSup f μ := by
  simp_rw [essSup]
  exact limsup_trim hm hf
#align measure_theory.ess_sup_trim MeasureTheory.essSup_trim

theorem snormEssSup_trim (hm : m ≤ m0) {f : α → E} (hf : StronglyMeasurable[m] f) :
    snormEssSup f (μ.trim hm) = snormEssSup f μ :=
  essSup_trim _ (@StronglyMeasurable.ennnorm _ m _ _ _ hf)
#align measure_theory.snorm_ess_sup_trim MeasureTheory.snormEssSup_trim

theorem snorm_trim (hm : m ≤ m0) {f : α → E} (hf : StronglyMeasurable[m] f) :
    snorm f p (μ.trim hm) = snorm f p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simpa only [h_top, snorm_exponent_top] using snormEssSup_trim hm hf
  simpa only [snorm_eq_snorm' h0 h_top] using snorm'_trim hm hf
#align measure_theory.snorm_trim MeasureTheory.snorm_trim

theorem snorm_trim_ae (hm : m ≤ m0) {f : α → E} (hf : AEStronglyMeasurable f (μ.trim hm)) :
    snorm f p (μ.trim hm) = snorm f p μ := by
  rw [snorm_congr_ae hf.ae_eq_mk, snorm_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)]
  exact snorm_trim hm hf.stronglyMeasurable_mk
#align measure_theory.snorm_trim_ae MeasureTheory.snorm_trim_ae

theorem memℒp_of_memℒp_trim (hm : m ≤ m0) {f : α → E} (hf : Memℒp f p (μ.trim hm)) : Memℒp f p μ :=
  ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf.1,
    (le_of_eq (snorm_trim_ae hm hf.1).symm).trans_lt hf.2⟩
#align measure_theory.mem_ℒp_of_mem_ℒp_trim MeasureTheory.memℒp_of_memℒp_trim

end MeasureTheory
