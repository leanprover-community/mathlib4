/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Probability.Notation
import Mathlib.Probability.Cdf

/-! # Uniform distributions over ℝ

Define the uniform measure over the reals

## Main definitions
* `unifPdfReal`: the function `a b x ↦ Set.indicator (Icc a b) (1/(b-a)) x`,
  which is the probability density function for the (continuous) uniform distribution on the
  interval `[a,b]`.
* `unifPdf`: `ℝ≥0∞`-valued pdf,
  `unifPdf a b = ENNReal.ofReal (unifPdfReal a b)`.
* `unifMeasure`: a uniform measure on `ℝ`, parametrized by its left- and right-limits `a` and `b`.
* `unifCdfReal`: the CDF given by the definition of CDF in `ProbabilityTheory.Cdf` applied to the
  uniform measure.
-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section UnifPdf
/-- The pdf of the uniform distribution depending on its scale and rate-/
noncomputable
def unifPdfReal (a b x : ℝ) : ℝ :=
  Set.indicator (Icc a b) (fun _ ↦ 1 / (b-a)) x

/-- The pdf of the uniform distribution, as a function valued in `ℝ≥0∞` -/
noncomputable
def unifPdf (a b x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (unifPdfReal a b x)

lemma unifPdf_eq (a b x : ℝ) :
    unifPdf a b x = ENNReal.ofReal (Set.indicator (Icc a b) (fun _ ↦ 1/(b-a)) x) := rfl

lemma unifPdf_outside {a b x : ℝ} (hx : x < a ∨ x > b) : unifPdf a b x = 0 := by
  rw [unifPdf, unifPdfReal]
  rcases hx with h|h
  · rw [indicator_of_not_mem (not_mem_Icc_of_lt h)]
    simp
  · rw [indicator_of_not_mem (not_mem_Icc_of_gt h)]
    simp

lemma unifPdf_inside {a b x : ℝ} (hx : x ∈ Icc a b) :
    unifPdf a b x = ENNReal.ofReal (1/(b-a)) := by
  simp only [unifPdf_eq]
  congr
  exact indicator_of_mem hx fun _ ↦ 1 / (b - a)

/-- the Lebesgue integral of the uniform pdf over reals (-∞, a) equals 0 -/
lemma lintegral_unifPdf_left_a {a b x : ℝ} (hx : x ≤ a) :
    ∫⁻ y in Iio x, unifPdf a b y = 0 := by
  rw [set_lintegral_congr_fun (g := fun _ ↦ 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · apply ae_of_all _
    intro _ hx1
    apply unifPdf_outside
    apply Or.inl
    exact LT.lt.trans_le hx1 hx

/-- the Lebesgue integral of the uniform pdf over reals (b, ∞) equals 0 -/
lemma lintegral_unifPdf_right_b {a b x : ℝ} (hx : b ≤ x) :
    ∫⁻ y in Ioi x, unifPdf a b y = 0 := by
  rw [set_lintegral_congr_fun (g := fun _ ↦ 0) measurableSet_Ioi]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · apply ae_of_all _
    intro _ hx1
    apply unifPdf_outside
    apply Or.inr
    exact gt_of_gt_of_ge hx1 hx

/-- The uniform pdf is measurable -/
lemma measurable_unifPdfReal (a b : ℝ) : Measurable (unifPdfReal a b) := by
  apply Measurable.indicator <;> measurability

/-- The uniform pdf is positive on `[a,b]` -/
lemma uniformPdfReal_pos {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b):
    0 < unifPdfReal a b x := by
  rwa [unifPdfReal, Set.indicator_of_mem hx, one_div, inv_pos, sub_pos]

/-- The uniform pdf is nonnegative -/
lemma unifPdfReal_nonneg {a b : ℝ} (hab : a < b) (x : ℝ):
    0 ≤ unifPdfReal a b x := by
  unfold unifPdfReal
  apply Set.indicator_nonneg
  intro _ _
  simp only [one_div, inv_nonneg, sub_nonneg, LT.lt.le hab]

open Measure

/-- The pdf of the uniform distribution integrates to 1 -/
@[simp]
lemma lintegral_unifPdf_eq_one {a b : ℝ} :
    ∫⁻ x, unifPdf a b x = 1 := by
  have leftSide : ∫⁻ x in Iio a, unifPdf a b x = 0 := by
    rw [set_lintegral_congr_fun measurableSet_Iio]
    · exact lintegral_zero
    · exact ae_of_all _ (fun x (hx : x < a) ↦ unifPdf_outside (Or.inl hx))
  have middleSide : ∫⁻ x in Icc a b, unifPdf a b x =
      ∫⁻ x in Icc a b, ENNReal.ofReal (1/(b-a)) := by
    apply set_lintegral_congr_fun measurableSet_Icc
    apply (ae_of_all _ (fun _ ↦ unifPdf_inside))
  have rightSide : ∫⁻ x in Ioi b, unifPdf a b x = 0 := by
    rw [set_lintegral_congr_fun measurableSet_Ioi]
    · exact lintegral_zero
    · exact ae_of_all _ (fun x (hx : b < x) ↦ unifPdf_outside (Or.inr hx))
  rw [← ENNReal.toReal_eq_one_iff, ← lintegral_add_compl _ measurableSet_Ici, compl_Ici,
    leftSide, add_zero]
  --rw [← lintegral_inter_add_diff _ (Ici a) (measurableSet_Icc a b)]

  · simp_rw [integral_Ici_eq_integral_Ioi, mul_assoc]
    rw [integral_mul_left, integral_rpow_mul_exp_neg_mul_Ioi ha hr, div_mul_eq_mul_div,
      ← mul_assoc, mul_div_assoc, div_self (Gamma_pos_of_pos ha).ne', mul_one,
      div_rpow zero_le_one hr.le, one_rpow, mul_one_div, div_self (rpow_pos_of_pos hr _).ne']
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ici]
    exact ae_of_all _ (fun x (hx : 0 ≤ x) ↦ by positivity)
  · apply (measurable_gammaPdfReal a r).aestronglyMeasurable.congr
    refine (ae_restrict_iff' measurableSet_Ici).mpr <| ae_of_all _ fun x (hx : 0 ≤ x) ↦ ?_
    simp_rw [gammaPdfReal, eq_true_intro hx, ite_true]

end UnifPdf

open MeasureTheory

/-- Measure defined by the uniform distribution -/
noncomputable
def unifMeasure (a b : ℝ) : Measure ℝ :=
  volume.withDensity (unifPdf a b)

lemma isProbabilityMeasureUnif {a b : ℝ} :
    IsProbabilityMeasure (unifMeasure a b) where
  measure_univ := by simp [gammaMeasure, lintegral_gammaPdf_eq_one ha hr]

section UnifCdf

/-- CDF of the uniform distribution -/
noncomputable
def unifCdfReal (a b : ℝ) : StieltjesFunction :=
  cdf (unifMeasure a b)

lemma unifCdfReal_eq_integral {a b : ℝ} (x : ℝ) :
    unifCdfReal a b x = ∫ x in Iic x, unifPdfReal a b x := by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasureGamma ha hr
  rw [gammaCdfReal, cdf_eq_toReal, gammaMeasure, withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun b ↦ by simp only [Pi.zero_apply, gammaPdfReal_nonneg ha hr]
  · exact (measurable_gammaPdfReal a r).aestronglyMeasurable.restrict

lemma unifCdfReal_eq_lintegral {a b : ℝ} (x : ℝ) :
    unifCdfReal a b x = ENNReal.toReal (∫⁻ x in Iic x, unifPdf a r x) := by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasureGamma ha hr
  simp only [gammaPdf, gammaCdfReal, cdf_eq_toReal]
  simp only [gammaMeasure, measurableSet_Iic, withDensity_apply, gammaPdf]

end UnifCdf
