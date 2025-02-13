/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

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

theorem eLpNorm'_trim (hm : m ≤ m0) {f : α → E} (hf : StronglyMeasurable[m] f) :
    eLpNorm' f q (μ.trim hm) = eLpNorm' f q μ := by
  simp_rw [eLpNorm']
  congr 1
  refine lintegral_trim hm ?_
  refine @Measurable.pow_const _ _ _ _ _ _ _ m _ (@Measurable.coe_nnreal_ennreal _ m _ ?_) q
  apply @StronglyMeasurable.measurable
  exact @StronglyMeasurable.nnnorm α m _ _ _ hf

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

theorem essSup_trim (hm : m ≤ m0) {f : α → ℝ≥0∞} (hf : Measurable[m] f) :
    essSup f (μ.trim hm) = essSup f μ := by
  simp_rw [essSup]
  exact limsup_trim hm hf

theorem eLpNormEssSup_trim (hm : m ≤ m0) {f : α → E} (hf : StronglyMeasurable[m] f) :
    eLpNormEssSup f (μ.trim hm) = eLpNormEssSup f μ :=
  essSup_trim _ (@StronglyMeasurable.enorm _ m _ _ _ hf)

theorem eLpNorm_trim (hm : m ≤ m0) {f : α → E} (hf : StronglyMeasurable[m] f) :
    eLpNorm f p (μ.trim hm) = eLpNorm f p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simpa only [h_top, eLpNorm_exponent_top] using eLpNormEssSup_trim hm hf
  simpa only [eLpNorm_eq_eLpNorm' h0 h_top] using eLpNorm'_trim hm hf

theorem eLpNorm_trim_ae (hm : m ≤ m0) {f : α → E} (hf : AEStronglyMeasurable[m] f (μ.trim hm)) :
    eLpNorm f p (μ.trim hm) = eLpNorm f p μ := by
  rw [eLpNorm_congr_ae hf.ae_eq_mk, eLpNorm_congr_ae (ae_eq_of_ae_eq_trim hf.ae_eq_mk)]
  exact eLpNorm_trim hm hf.stronglyMeasurable_mk

theorem memℒp_of_memℒp_trim (hm : m ≤ m0) {f : α → E} (hf : Memℒp f p (μ.trim hm)) : Memℒp f p μ :=
  ⟨aestronglyMeasurable_of_aestronglyMeasurable_trim hm hf.1,
    (le_of_eq (eLpNorm_trim_ae hm hf.1).symm).trans_lt hf.2⟩

end MeasureTheory
