/-
Copyright (c) 2024 Alvan Arulandu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvan Arulandu
-/
import Mathlib.Probability.Notation
import Mathlib.Probability.Cdf
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Field.Defs

/-! # Pareto distributions over ℝ

Define the pareto measure over the reals.

## Main definitions
* `paretoPDFReal`: the function `t r x ↦ r * t ^ r / x ^ (r + 1)`
  for `t ≤ x` or `0` else, which is the probability density function of a pareto distribution with
  scale `t` and shape `r` (when `ht : 0 < t ` and `hr : 0 < r`).
* `paretoPDF`: `ℝ≥0∞`-valued pdf,
  `paretoPDF a r = ENNReal.ofReal (paretoPDFReal a r)`.
* `paretoMeasure`: a pareto measure on `ℝ`, parametrized by its scale `t` and shape `r`.
* `paretoCDFReal`: the CDF given by the definition of CDF in `ProbabilityTheory.CDF` applied to the
  pareto measure.
-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section ParetoPDF

/-- The pdf of the pareto distribution depending on its scale and rate -/
noncomputable
def paretoPDFReal (t r x : ℝ) : ℝ :=
  if t ≤ x then r * t ^ r / x ^ (r + 1) else 0

/-- The pdf of the pareto distribution, as a function valued in `ℝ≥0∞` -/
noncomputable
def paretoPDF (t r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (paretoPDFReal t r x)

lemma paretoPDF_eq (t r x : ℝ) :
    paretoPDF t r x = ENNReal.ofReal (if t ≤ x then r * t ^ r / (x ^ (r + 1)) else 0) := rfl

lemma paretoPDF_of_neg {t r x : ℝ} (hx : x < t) : paretoPDF t r x = 0 := by
  simp only [paretoPDF_eq, if_neg (not_le.mpr hx), ENNReal.ofReal_zero]

lemma paretoPDF_of_nonneg {t r x : ℝ} (hx : t ≤ x) :
    paretoPDF t r x = ENNReal.ofReal (r * t ^ r / (x ^ (r + 1))) := by
  simp only [paretoPDF_eq, if_pos hx]

/-- The Lebesgue integral of the pareto pdf over reals < t equals 0 -/
lemma lintegral_paretoPDF_of_nonpos {t r x : ℝ} (hx : x < t) :
    ∫⁻ y in Iio x, paretoPDF t r y = 0 := by
  rw [set_lintegral_congr_fun (g := fun _ ↦ 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · simp only [paretoPDF_eq, ge_iff_le, ENNReal.ofReal_eq_zero]
    filter_upwards with a (_ : a < _)
    rw [if_neg (by linarith)]

/-- The pareto pdf is measurable. -/
@[measurability]
lemma measurable_paretoPDFReal (t r : ℝ) : Measurable (paretoPDFReal t r) :=
  Measurable.ite measurableSet_Ici ((measurable_id.pow_const _).const_div _) measurable_const

/-- The pareto pdf is strongly measurable -/
@[measurability]
 lemma stronglyMeasurable_paretoPDFReal (t r : ℝ) :
     StronglyMeasurable (paretoPDFReal t r) :=
   (measurable_paretoPDFReal t r).stronglyMeasurable

/-- The pareto pdf is positive for all reals >= t -/
lemma paretoPDFReal_pos {t r x : ℝ} (ht : 0 < t) (hr : 0 < r) (hx : t ≤ x) :
  0 < paretoPDFReal t r x := by
  rw [paretoPDFReal, if_pos hx]
  have _ : 0 < x := by linarith
  positivity

/-- The pareto pdf is nonnegative -/
lemma paretoPDFReal_nonneg {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : ℝ) :
    0 ≤ paretoPDFReal t r x := by
  unfold paretoPDFReal
  split_ifs with h
  . have h2 := paretoPDFReal_pos ht hr h
    rw [paretoPDFReal, if_pos h] at h2
    linarith
  . positivity

open Measure


lemma integral_custom {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ∫ x : ℝ in Ioi t, r * t ^ r * x ^ (-(r + 1)) = 1 := by
    rw [integral_mul_left]
    have hp : -(r+1) < -1 := by linarith
    rw [integral_Ioi_rpow_of_lt hp ht]
    ring
    repeat rw [mul_assoc]
    rw [mul_comm]
    repeat rw [mul_assoc]

    have _ : t ^ r * (t ^ (-r) * (r⁻¹ * r)) = 1 := by sorry
    assumption

/-- The pdf of the pareto distribution integrates to 1 -/
@[simp]
lemma lintegral_paretoPDF_eq_one {t r : ℝ} (ht : 0 < t) (hr : 0 < r) :
    ∫⁻ x, paretoPDF t r x = 1 := by
  have leftSide : ∫⁻ x in Iio t, paretoPDF t r x = 0 := by
    rw [set_lintegral_congr_fun measurableSet_Iio
      (ae_of_all _ (fun x (hx : x < t) ↦ paretoPDF_of_neg hx)), lintegral_zero]
  have rightSide : ∫⁻ x in Ici t, paretoPDF t r x =
      ∫⁻ x in Ici t, ENNReal.ofReal (r * t ^ r / x ^ (r + 1)) :=
    set_lintegral_congr_fun measurableSet_Ici (ae_of_all _ (fun _ ↦ paretoPDF_of_nonneg))
  rw [← ENNReal.toReal_eq_one_iff, ← lintegral_add_compl _ measurableSet_Ici, compl_Ici,
    leftSide, rightSide, add_zero, ← integral_eq_lintegral_of_nonneg_ae]
  . rw [integral_Ici_eq_integral_Ioi]
    sorry
  . rw [EventuallyLE, ae_restrict_iff' measurableSet_Ici]
    exact ae_of_all _ (fun x (hx : t ≤ x) ↦ by
      have _ : 0 < x := by linarith
      positivity
    )
  . apply (measurable_paretoPDFReal t r).aestronglyMeasurable.congr
    refine (ae_restrict_iff' measurableSet_Ici).mpr <| ae_of_all _ fun x (hx : t ≤ x) ↦ ?_
    simp_rw [paretoPDFReal, eq_true_intro hx, ite_true]
end ParetoPDF

open MeasureTheory

/-- Measure defined by the pareto distribution -/
noncomputable
def paretoMeasure (a r : ℝ) : Measure ℝ :=
  volume.withDensity (paretoPDF a r)

lemma isProbabilityMeasurePareto {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure (paretoMeasure a r) where
  measure_univ := by simp [paretoMeasure, lintegral_paretoPDF_eq_one ha hr]

section ParetoCDF

/-- CDF of the pareto distribution -/
noncomputable
def paretoCDFReal (a r : ℝ) : StieltjesFunction :=
  cdf (paretoMeasure a r)

lemma paretoCDFReal_eq_integral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    paretoCDFReal a r x = ∫ x in Iic x, paretoPDFReal a r x := by
  have : IsProbabilityMeasure (paretoMeasure a r) := isProbabilityMeasurePareto ha hr
  rw [paretoCDFReal, cdf_eq_toReal, paretoMeasure, withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun b ↦ by simp only [Pi.zero_apply, paretoPDFReal_nonneg ha hr]
  · exact (measurable_paretoPDFReal a r).aestronglyMeasurable.restrict

lemma paretoCDFReal_eq_lintegral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    paretoCDFReal a r x = ENNReal.toReal (∫⁻ x in Iic x, paretoPDF a r x) := by
  have : IsProbabilityMeasure (paretoMeasure a r) := isProbabilityMeasurePareto ha hr
  simp only [paretoPDF, paretoCDFReal, cdf_eq_toReal]
  simp only [paretoMeasure, measurableSet_Iic, withDensity_apply, paretoPDF]

end ParetoCDF
