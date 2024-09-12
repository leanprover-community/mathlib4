/-
Copyright (c) 2024 Alvan Caleb Arulandu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvan Caleb Arulandu.
-/
import Mathlib.Probability.Notation
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Beta distributions over ℝ

Define the beta measure over the reals.

## Main definitions
* `betaPDFReal`: the function `a b x ↦ 1 / (betaIntegral a b) * x ^ (a - 1) * (1 - x) ^ (b - 1)`
  for `0 ≤ x` or `0` else, which is the probability density function of a beta distribution with
  shape `a` and rate `r` (when `ha : 0 < a ` and `hb: 0 < b`).
* `betaPDF`: `ℝ≥0∞`-valued pdf,
  `betaPDF a b = ENNReal.ofReal (betaPDFReal a b)`.
* `betaMeasure`: a beta measure on `ℝ`, parametrized by its shape `a` and rate `r`.
* `betaCDFReal`: the CDF given by the definition of CDF in `ProbabilityTheory.CDF` applied to the
  beta measure.
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

section BetaPDF

/-- The pdf of the beta distribution depending on its scale and rate -/
noncomputable
def betaPDFReal (a b x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then 1 / (Beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1) else 0

/-- The pdf of the beta distribution, as a function valued in `ℝ≥0∞` -/
noncomputable
def betaPDF (a b x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (betaPDFReal a b x)

lemma betaPDF_eq (a b x : ℝ) :
    betaPDF a b x = ENNReal.ofReal (if 0 < x ∧ x < 1
    then 1 / (Beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1) else 0) := rfl

lemma betaPDF_of_non01 {a b x : ℝ} (hx : x <= 0 ∨ x >= 1) : betaPDF a b x = 0 := by
  rw [betaPDF_eq]
  have hx_n : ¬(0 < x ∧ x < 1) := by
    simp only [not_and_or, not_lt]
    exact hx

  rw [if_neg hx_n, ENNReal.ofReal_zero]

lemma betaPDF_of_01 {a b x : ℝ} (hx : 0 < x ∧ x < 1) :
    betaPDF a b x = ENNReal.ofReal (1 / (Beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1)) := by
  simp only [betaPDF_eq, if_pos hx]

/-- The Lebesgue integral of the beta pdf over nonpositive reals equals 0 -/
lemma lintegral_betaPDF_of_nonpos {x a b : ℝ} (hx : x ≤ 0) :
    ∫⁻ y in Iio x, betaPDF a b y = 0 := by
  rw [setLIntegral_congr_fun (g := fun _ ↦ 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · simp only [betaPDF_eq, ENNReal.ofReal_eq_zero]
    filter_upwards with a (_ : a < _)
    have hx_a : ¬(0 < a ∧ a < 1) := by
      simp only [not_and_or, not_lt]
      left
      linarith

    rw [if_neg hx_a]

lemma lintegral_betaPDF_of_1up {x a b : ℝ} (hx : x ≥ 1) :
    ∫⁻ y in Ioi x, betaPDF a b y = 0 := by
  rw [setLIntegral_congr_fun (g := fun _ ↦ 0) measurableSet_Ioi]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · simp only [betaPDF_eq, ENNReal.ofReal_eq_zero]
    filter_upwards with a (_ : a > _)
    have hx_a : ¬(0 < a ∧ a < 1) := by
      simp only [not_and_or, not_lt]
      right
      linarith

    rw [if_neg hx_a]

/-- The beta pdf is measurable. -/
@[measurability]
lemma measurable_betaPDFReal (a b : ℝ) : Measurable (betaPDFReal a b) := by
  apply Measurable.ite
  apply measurableSet_Ioo
  · have h1 : Measurable fun x ↦ (1 / (Beta a b) * x ^ (a - 1)) := by
      exact (measurable_id'.pow_const _).const_mul _
    have h2 : Measurable fun x:ℝ ↦ ((1 - x) ^ (b - 1)) := by
      exact (measurable_const.sub' measurable_id').pow_const _
    exact h1.mul h2
  · exact measurable_const

/-- The beta pdf is strongly measurable -/
@[measurability]
 lemma stronglyMeasurable_betaPDFReal (a b : ℝ) :
     StronglyMeasurable (betaPDFReal a b) :=
   (measurable_betaPDFReal a b).stronglyMeasurable

/-- The beta pdf is positive for in support -/
lemma betaPDFReal_pos {x a b : ℝ} (ha : 0 < a) (hb: 0 < b) (hx : 0 < x ∧ x < 1) :
    0 < betaPDFReal a b x := by
  simp only [betaPDFReal, if_pos hx]
  have hx_pos : x > 0 := hx.left

  have h0 : 0 < x ^ (a - 1) := by sorry
  have h1 : 0 < x ^ (a - 1) * (1 - x) ^ (b - 1) := by sorry
  have h2 : 0 < (1 / Beta a b) := by sorry

  sorry

open Measure

/-- The pdf of the beta distribution integrates to 1 -/
@[simp]
lemma lintegral_betaPDF_eq_one {a b : ℝ} (ha : 0 < a) (hb: 0 < b) :
    ∫⁻ x, betaPDF a b x = 1 := by
  have left : ∫⁻ x in Iic 0, betaPDF a b x = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Iic
      (ae_of_all _ (fun x (hx : x ≤ 0) ↦ betaPDF_of_non01 (Or.inl hx))), lintegral_zero]

  have middle : ∫⁻ x in Ioo 0 1, betaPDF a b x =
      ∫⁻ x in Ioo 0 1, ENNReal.ofReal (1 / (Beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1)) :=
    setLIntegral_congr_fun measurableSet_Ioo (ae_of_all _ (fun _ ↦ betaPDF_of_01))

  have right : ∫⁻ x in Ici 1, betaPDF a b x = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ici
      (ae_of_all _ (fun x (hx : x ≥ 1) ↦ betaPDF_of_non01 (Or.inr hx))), lintegral_zero]

  -- break up the integral


  -- solve it
  sorry
end BetaPDF

open MeasureTheory

/-- Measure defined by the beta distribution -/
noncomputable
def betaMeasure (a b : ℝ) : Measure ℝ :=
  volume.withDensity (betaPDF a b)

lemma isProbabilityMeasureBeta {a b : ℝ} (ha : 0 < a) (hb: 0 < b) :
    IsProbabilityMeasure (betaMeasure a b) where
  measure_univ := by simp [betaMeasure, lintegral_betaPDF_eq_one ha hb]

section BetaCDF

/-- CDF of the beta distribution -/
noncomputable
def betaCDFReal (a b : ℝ) : StieltjesFunction :=
  cdf (betaMeasure a b)

lemma betaCDFReal_eq_integral {a b : ℝ} (ha : 0 < a) (hb: 0 < b) (x : ℝ) :
    betaCDFReal a b x = ∫ x in Iic x, betaPDFReal a b x := by
  have : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  rw [betaCDFReal, cdf_eq_toReal, betaMeasure, withDensity_apply _ measurableSet_Iic]
  refine (integral_eq_lintegral_of_nonneg_ae ?_ ?_).symm
  · exact ae_of_all _ fun b ↦ by sorry
  · exact (measurable_betaPDFReal a b).aestronglyMeasurable.restrict

lemma betaCDFReal_eq_lintegral {a b : ℝ} (ha : 0 < a) (hb: 0 < b) (x : ℝ) :
    betaCDFReal a b x = ENNReal.toReal (∫⁻ x in Iic x, betaPDF a b x) := by
  have : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  simp only [betaPDF, betaCDFReal, cdf_eq_toReal]
  simp only [betaMeasure, measurableSet_Iic, withDensity_apply, betaPDF]

end BetaCDF

end ProbabilityTheory
