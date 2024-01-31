/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker, Kexing Ying
-/
import Mathlib.Probability.Notation
import Mathlib.Probability.Cdf
import Mathlib.Probability.Density

/-! # Uniform distributions

Defines the uniform distribution for any set with finite measure.

## Main definitions
* `uniformMeasure s` : The uniform measure on `s` is the
  the measure restricted to `s`, normalized.
* `IsUniform X s ℙ μ` : A random variable `X` has uniform distribution on `s` under `ℙ` if the
  push-forward measure agrees with the rescaled restricted volume measure `μ`.
-/

open scoped Classical MeasureTheory NNReal ENNReal

open TopologicalSpace MeasureTheory.Measure

noncomputable section

namespace MeasureTheory

variable {E : Type*} [MeasurableSpace E] {m : Measure E} {μ : Measure E}

/-- A measure is a uniform measure for a set `s` if it is the rescaled restriction of the volume to
this set.  -/
def uniformMeasure (s : Set E) (μ : Measure E) : Measure E := (μ s)⁻¹ • μ.restrict s

namespace UniformMeasure

theorem absolutelyContinuous {s : Set E} :
    uniformMeasure s μ ≪ μ := by
  intro t ht
  unfold uniformMeasure
  rw [smul_apply, smul_eq_mul]
  apply mul_eq_zero.mpr
  refine Or.inr (le_antisymm ?_ (zero_le _))
  exact ht ▸ restrict_apply_le s t

theorem uniformMeasure_apply {s : Set E} {A : Set E}
    (hA : MeasurableSet A) : uniformMeasure s μ A = μ (s ∩ A) / μ s := by
  unfold uniformMeasure
  rw [smul_apply, restrict_apply hA, ENNReal.div_eq_inv_mul, smul_eq_mul, Set.inter_comm]

theorem isProbabilityMeasure {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞) :
    IsProbabilityMeasure (uniformMeasure s μ) :=
  ⟨by
    unfold uniformMeasure
    simp only [smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, MeasurableSet.univ,
      restrict_apply, Set.univ_inter, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hns hnt⟩

theorem toMeasurable_eq {s : Set E} :
    uniformMeasure (toMeasurable μ s) μ = uniformMeasure s μ:= by
  unfold uniformMeasure
  by_cases hnt : μ s = ∞
  · simp [hnt]
  · simp [restrict_toMeasurable hnt]

end UniformMeasure

namespace pdf

variable {Ω : Type*}

variable {_ : MeasurableSpace Ω} {ℙ : Measure Ω}

/-- A random variable `X` has uniform distribution on `s` if its push-forward measure is
`(μ s)⁻¹ • μ.restrict s`. -/
def IsUniform (X : Ω → E) (s : Set E) (ℙ : Measure Ω) (μ : Measure E := by volume_tac) :=
  (map X ℙ) = uniformMeasure s μ -- was `(μ s)⁻¹ • μ.restrict s
#align measure_theory.pdf.is_uniform MeasureTheory.pdf.IsUniform

namespace IsUniform

theorem aemeasurable {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) : AEMeasurable X ℙ := by
  dsimp [IsUniform, uniformMeasure] at hu
  by_contra h
  rw [map_of_not_aemeasurable h] at hu
  apply zero_ne_one' ℝ≥0∞
  calc
    0 = (0 : Measure E) Set.univ := rfl
    _ = _ := by rw [hu, smul_apply, restrict_apply MeasurableSet.univ,
      Set.univ_inter, smul_eq_mul, ENNReal.inv_mul_cancel hns hnt]

theorem absolutelyContinuous {X : Ω → E} {s : Set E} (hu : IsUniform X s ℙ μ) : map X ℙ ≪ μ := by
  rw [hu]
  exact UniformMeasure.absolutelyContinuous

theorem measure_preimage {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) {A : Set E} (hA : MeasurableSet A) :
    ℙ (X ⁻¹' A) = μ (s ∩ A) / μ s := by
  rw [← map_apply_of_aemeasurable (hu.aemeasurable hns hnt) hA, hu,
    ← UniformMeasure.uniformMeasure_apply hA]
#align measure_theory.pdf.is_uniform.measure_preimage MeasureTheory.pdf.IsUniform.measure_preimage

theorem isProbabilityMeasure {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) : IsProbabilityMeasure ℙ :=
  ⟨by
    have : X ⁻¹' Set.univ = Set.univ := Set.preimage_univ
    rw [← this, hu.measure_preimage hns hnt MeasurableSet.univ, Set.inter_univ,
      ENNReal.div_self hns hnt]⟩
#align measure_theory.pdf.is_uniform.is_probability_measure MeasureTheory.pdf.IsUniform.isProbabilityMeasure

theorem toMeasurable_iff {X : Ω → E} {s : Set E} :
    IsUniform X (toMeasurable μ s) ℙ μ ↔ IsUniform X s ℙ μ := by
  unfold IsUniform
  rw [UniformMeasure.toMeasurable_eq]

protected theorem toMeasurable {X : Ω → E} {s : Set E} (hu : IsUniform X s ℙ μ) :
    IsUniform X (toMeasurable μ s) ℙ μ := by
  unfold IsUniform at *
  rwa [UniformMeasure.toMeasurable_eq]

theorem hasPDF {X : Ω → E} {s : Set E} (hns : μ s ≠ 0) (hnt : μ s ≠ ∞)
    (hu : IsUniform X s ℙ μ) : HasPDF X ℙ μ := by
  let t := toMeasurable μ s
  apply hasPDF_of_map_eq_withDensity (hu.aemeasurable hns hnt) (t.indicator ((μ t)⁻¹ • 1)) <|
    (measurable_one.aemeasurable.const_smul (μ t)⁻¹).indicator (measurableSet_toMeasurable μ s)
  rw [hu, withDensity_indicator (measurableSet_toMeasurable μ s), withDensity_smul _ measurable_one,
    withDensity_one, restrict_toMeasurable hnt, measure_toMeasurable]
  rfl
#align measure_theory.pdf.is_uniform.has_pdf MeasureTheory.pdf.IsUniform.hasPDF

theorem pdf_eq_zero_of_measure_eq_zero_or_top {X : Ω → E} {s : Set E}
    (hu : IsUniform X s ℙ μ) (hμs : μ s = 0 ∨ μ s = ∞) : pdf X ℙ μ =ᵐ[μ] 0 := by
  rcases hμs with H|H
  · simp only [IsUniform, uniformMeasure, H, ENNReal.inv_zero, restrict_eq_zero.mpr H,
    smul_zero] at hu
    simp [pdf, hu]
  · simp only [IsUniform, uniformMeasure, H, ENNReal.inv_top, zero_smul] at hu
    simp [pdf, hu]

theorem pdf_eq {X : Ω → E} {s : Set E} (hms : MeasurableSet s)
    (hu : IsUniform X s ℙ μ) : pdf X ℙ μ =ᵐ[μ] s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) := by
  by_cases hnt : μ s = ∞
  · simp [pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inr hnt), hnt]
  by_cases hns : μ s = 0
  · filter_upwards [measure_zero_iff_ae_nmem.mp hns,
      pdf_eq_zero_of_measure_eq_zero_or_top hu (Or.inl hns)] with x hx h'x
    simp [hx, h'x, hns]
  have : HasPDF X ℙ μ := hasPDF hns hnt hu
  have : IsProbabilityMeasure ℙ := isProbabilityMeasure hns hnt hu
  apply (eq_of_map_eq_withDensity _ _).mp
  · rw [hu, withDensity_indicator hms,
    withDensity_smul _ measurable_one, withDensity_one]
    rfl
  · exact (measurable_one.aemeasurable.const_smul (μ s)⁻¹).indicator hms

theorem pdf_toReal_ae_eq {X : Ω → E} {s : Set E} (hms : MeasurableSet s)
    (hX : IsUniform X s ℙ μ) :
    (fun x => (pdf X ℙ μ x).toReal) =ᵐ[μ] fun x =>
      (s.indicator ((μ s)⁻¹ • (1 : E → ℝ≥0∞)) x).toReal :=
  Filter.EventuallyEq.fun_comp (pdf_eq hms hX) ENNReal.toReal
#align measure_theory.pdf.is_uniform.pdf_to_real_ae_eq MeasureTheory.pdf.IsUniform.pdf_toReal_ae_eq

variable {X : Ω → ℝ} {s : Set ℝ}

theorem mul_pdf_integrable (hcs : IsCompact s) (huX : IsUniform X s ℙ) :
    Integrable fun x : ℝ => x * (pdf X ℙ volume x).toReal := by
  by_cases hnt : volume s = 0 ∨ volume s = ∞
  · have I : Integrable (fun x ↦ x * ENNReal.toReal (0)) := by simp
    apply I.congr
    filter_upwards [pdf_eq_zero_of_measure_eq_zero_or_top huX hnt] with x hx
    simp [hx]
  simp only [not_or] at hnt
  have : IsProbabilityMeasure ℙ := isProbabilityMeasure hnt.1 hnt.2 huX
  constructor
  · exact aestronglyMeasurable_id.mul
      (measurable_pdf X ℙ).aemeasurable.ennreal_toReal.aestronglyMeasurable
  refine' hasFiniteIntegral_mul (pdf_eq hcs.measurableSet huX) _
  set ind := (volume s)⁻¹ • (1 : ℝ → ℝ≥0∞)
  have : ∀ x, ↑‖x‖₊ * s.indicator ind x = s.indicator (fun x => ‖x‖₊ * ind x) x := fun x =>
    (s.indicator_mul_right (fun x => ↑‖x‖₊) ind).symm
  simp only [this, lintegral_indicator _ hcs.measurableSet, mul_one, Algebra.id.smul_eq_mul,
    Pi.one_apply, Pi.smul_apply]
  rw [lintegral_mul_const _ measurable_nnnorm.coe_nnreal_ennreal]
  exact (ENNReal.mul_lt_top (set_lintegral_lt_top_of_isCompact hnt.2 hcs continuous_nnnorm).ne
    (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.mpr hnt.1)).ne).ne
#align measure_theory.pdf.is_uniform.mul_pdf_integrable MeasureTheory.pdf.IsUniform.mul_pdf_integrable

/-- A real uniform random variable `X` with support `s` has expectation
`(λ s)⁻¹ * ∫ x in s, x ∂λ` where `λ` is the Lebesgue measure. -/
theorem integral_eq (huX : IsUniform X s ℙ) :
    ∫ x, X x ∂ℙ = (volume s)⁻¹.toReal * ∫ x in s, x := by
  rw [← smul_eq_mul, ← integral_smul_measure]
  dsimp [IsUniform, uniformMeasure] at huX
  rw [← huX]
  by_cases hX : AEMeasurable X ℙ
  · exact (integral_map hX aestronglyMeasurable_id).symm
  · rw [map_of_not_aemeasurable hX, integral_zero_measure, integral_non_aestronglyMeasurable]
    rwa [aestronglyMeasurable_iff_aemeasurable]
#align measure_theory.pdf.is_uniform.integral_eq MeasureTheory.pdf.IsUniform.integral_eq

end IsUniform

lemma uniformMeasure.IsUniform {s : Set E} : IsUniform (id : E → E) s (uniformMeasure s μ) μ := by
  unfold IsUniform
  rw [map_id]

end pdf
