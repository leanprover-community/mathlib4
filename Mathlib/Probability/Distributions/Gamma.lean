/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Probability.Notation
import Mathlib.Probability.Cdf
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # Gamma distributions over ℝ

Define the gamma measure over the reals.

## Main definitions
* `gammaPdfReal`: the function `a r x ↦ r ^ a / (Gamma a) * x ^ (a-1) * exp (-(r * x))`
  for `0 ≤ x` or `0` else, which is the probability density function of a gamma distribution with
  shape `a` and rate `r` (when `ha : 0 < a ` and `hr : 0 < r`).
* `gammaPdf`: `ℝ≥0∞`-valued pdf,
  `gammaPdf a r = ENNReal.ofReal (gammaPdfReal a r)`.
* `gammaMeasure`: a gamma measure on `ℝ`, parametrized by its shape `a` and rate `r`.
* `gammaCdfReal`: the CDF given by the definition of CDF in `ProbabilityTheory.Cdf` applied to the
  gamma measure.
-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

/-- A Lebesgue Integral from -∞ to y can be expressed as the sum of one from -∞ to 0 and 0 to x -/
lemma lintegral_Iic_eq_lintegral_Iio_add_Icc {y z : ℝ} (f : ℝ → ℝ≥0∞) (hzy : z ≤ y) :
    ∫⁻ x in Iic y, f x = (∫⁻ x in Iio z, f x) + ∫⁻ x in Icc z y, f x := by
  rw [← Iio_union_Icc_eq_Iic hzy, lintegral_union measurableSet_Icc]
  rw [Set.disjoint_iff]
  rintro x ⟨h1 : x < _, h2, _⟩
  linarith

namespace ProbabilityTheory

section GammaPdf

/-- The pdf of the gamma distribution depending on its scale and rate -/
noncomputable
def gammaPdfReal (a r x : ℝ) : ℝ :=
  if 0 ≤ x then r ^ a / (Gamma a) * x ^ (a-1) * exp (-(r * x)) else 0

/-- The pdf of the gamma distribution, as a function valued in `ℝ≥0∞` -/
noncomputable
def gammaPdf (a r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gammaPdfReal a r x)

lemma gammaPdf_eq (a r x : ℝ) :
    gammaPdf a r x = ENNReal.ofReal (if 0 ≤ x then
    r ^ a / (Gamma a) * x ^ (a-1) * exp (-(r * x)) else 0) := rfl

lemma gammaPdf_of_neg {a r x : ℝ} (hx : x < 0) : gammaPdf a r x = 0 := by
  simp only [gammaPdf_eq, if_neg (not_le.mpr hx), ENNReal.ofReal_zero]

lemma gammaPdf_of_nonneg {a r x : ℝ} (hx : 0 ≤ x) :
    gammaPdf a r x = ENNReal.ofReal (r ^ a / (Gamma a) * x ^ (a-1) * exp (-(r * x))) := by
  simp only [gammaPdf_eq, if_pos hx]

/-- The Lebesgue integral of the gamma pdf over nonpositive reals equals 0 -/
lemma lintegral_gammaPdf_of_nonpos {x a r : ℝ} (hx : x ≤ 0) :
    ∫⁻ y in Iio x, gammaPdf a r y = 0 := by
  rw [set_lintegral_congr_fun (g := fun _ ↦ 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · simp only [gammaPdf_eq, ge_iff_le, ENNReal.ofReal_eq_zero]
    apply ae_of_all _ fun a (_ : a < _) ↦ by rw [if_neg (by linarith)]

/-- The gamma pdf is measurable. -/
@[measurability]
lemma measurable_gammaPdfReal (a r : ℝ) : Measurable (gammaPdfReal a r) :=
  Measurable.ite measurableSet_Ici (((measurable_id'.pow_const _).const_mul _).mul
    (measurable_id'.const_mul _).neg.exp) measurable_const

/-- The gamma pdf is strongly measurable -/
@[measurability]
 lemma stronglyMeasurable_gammaPdfReal (a r : ℝ) :
     StronglyMeasurable (gammaPdfReal a r) :=
   (measurable_gammaPdfReal a r).stronglyMeasurable

/-- The gamma pdf is positive for all positive reals -/
lemma gammaPdfReal_pos {x a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hx : 0 < x) :
    0 < gammaPdfReal a r x := by
  simp only [gammaPdfReal, if_pos hx.le]
  positivity

/-- The gamma pdf is nonnegative -/
lemma gammaPdfReal_nonneg {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    0 ≤ gammaPdfReal a r x := by
  unfold gammaPdfReal
  split_ifs <;> positivity

open Measure

/-- The pdf of the gamma distribution integrates to 1 -/
@[simp]
lemma lintegral_gammaPdf_eq_one {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫⁻ x, gammaPdf a r x = 1 := by
  have leftSide : ∫⁻ x in Iio 0, gammaPdf a r x = 0 := by
    rw [set_lintegral_congr_fun measurableSet_Iio
      (ae_of_all _ (fun x (hx : x < 0) ↦ gammaPdf_of_neg hx)), lintegral_zero]
  have rightSide : ∫⁻ x in Ici 0, gammaPdf a r x =
      ∫⁻ x in Ici 0, ENNReal.ofReal (r ^ a / Gamma a * x ^ (a - 1) * exp (-(r * x))) :=
    set_lintegral_congr_fun measurableSet_Ici (ae_of_all _ (fun _ ↦ gammaPdf_of_nonneg))
  rw [← ENNReal.toReal_eq_one_iff, ← lintegral_add_compl _ measurableSet_Ici, compl_Ici,
    leftSide, rightSide, add_zero, ← integral_eq_lintegral_of_nonneg_ae]
  · simp_rw [integral_Ici_eq_integral_Ioi, mul_assoc]
    rw [integral_mul_left, integral_rpow_mul_exp_neg_mul_Ioi ha hr, div_mul_eq_mul_div,
      ← mul_assoc, mul_div_assoc, div_self (Gamma_pos_of_pos ha).ne', mul_one,
      div_rpow zero_le_one hr.le, one_rpow, mul_one_div, div_self (rpow_pos_of_pos hr _).ne']
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ici]
    exact ae_of_all _ (fun x (hx : 0 ≤ x) ↦ by positivity)
  · apply (measurable_gammaPdfReal a r).aestronglyMeasurable.congr
    refine (ae_restrict_iff' measurableSet_Ici).mpr <| ae_of_all _ fun x (hx : 0 ≤ x) ↦ ?_
    simp_rw [gammaPdfReal, eq_true_intro hx, ite_true]

end GammaPdf

open MeasureTheory

/-- Measure defined by the gamma distribution -/
noncomputable
def gammaMeasure (a r : ℝ) : Measure ℝ :=
  volume.withDensity (gammaPdf a r)

lemma isProbabilityMeasureGamma {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (gammaMeasure a r) where
  measure_univ := by simp [gammaMeasure, lintegral_gammaPdf_eq_one ha hr]

section GammaCdf

/-- CDF of the gamma distribution -/
noncomputable
def gammaCdfReal (a r : ℝ) : StieltjesFunction :=
  cdf (gammaMeasure a r)

lemma gammaCdfReal_eq_integral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    gammaCdfReal a r x = ∫ x in Iic x, gammaPdfReal a r x := by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasureGamma ha hr
  rw [gammaCdfReal, cdf_eq_toReal, gammaMeasure, withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun b ↦ by simp only [Pi.zero_apply, gammaPdfReal_nonneg ha hr]
  · exact (measurable_gammaPdfReal a r).aestronglyMeasurable.restrict

lemma gammaCdfReal_eq_lintegral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    gammaCdfReal a r x = ENNReal.toReal (∫⁻ x in Iic x, gammaPdf a r x) := by
  have : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasureGamma ha hr
  simp only [gammaPdf, gammaCdfReal, cdf_eq_toReal]
  simp only [gammaMeasure, measurableSet_Iic, withDensity_apply, gammaPdf]

end GammaCdf
