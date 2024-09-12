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

lemma betaReal_Integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
Beta a b = ∫ (x : ℝ) in Ioc 0 1, x ^ (a - 1) * (1 - x) ^ (b - 1) := by
  rw [Beta, Complex.betaIntegral]
  -- (1) + (2)
  -- type casting weirdness
  sorry

-- (1) prove complex.re integral = real integral [interval]
-- (2) prove real integral [interval] = real integral [bochner]

lemma betaIntervalIntegralPos {a b : ℝ} (ha: 0 < a) (hb : 0 < b) :
∫ (x : ℝ) in (0)..1, ↑x ^ (↑a - 1) * (1 - ↑x) ^ (↑b - 1) > 0 := by
  -- prove positivity of integral f(x) by showing f(x) > 0 in interior of (0, 1)
  sorry

lemma beta_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : Beta a b > 0 := by
  rw [Beta, Complex.betaIntegral]
  have h1 := betaIntervalIntegralPos ha hb
  -- (1)
  sorry

lemma betaPDFReal_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) : 0 ≤ betaPDFReal a b x := by
  unfold betaPDFReal
  split_ifs with ht
  · have h1 : x ^ (a - 1) ≥ 0 := rpow_nonneg (le_of_lt ht.left) (a - 1)
    have h2 : (1 - x) ^ (b - 1) ≥ 0 := by
      have hp : 1 - x ≥ 0 := by linarith
      exact rpow_nonneg hp (b - 1)
    have hbeta:= beta_pos ha hb
    positivity
  trivial

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
lemma measurable_betaPDFReal (a b : ℝ) : Measurable (betaPDFReal a b) :=
  Measurable.ite
    measurableSet_Ioo (((measurable_id'.pow_const _).const_mul _).mul
    ((measurable_const.sub' measurable_id').pow_const _))
    measurable_const

/-- The beta pdf is strongly measurable -/
@[measurability]
 lemma stronglyMeasurable_betaPDFReal (a b : ℝ) :
     StronglyMeasurable (betaPDFReal a b) :=
   (measurable_betaPDFReal a b).stronglyMeasurable

open Measure

/-- A Lebesgue Integral from -∞ to y can be expressed as the sum of one from -∞ to 0 and 0 to x -/
lemma lintegral_Iio_eq_lintegral_Iic_add_Ioo {y z : ℝ} (f : ℝ → ℝ≥0∞) (hzy : z < y) :
    ∫⁻ x in Iio y, f x = (∫⁻ x in Iic z, f x) + ∫⁻ x in Ioo z y, f x := by
  rw [← Iic_union_Ioo_eq_Iio hzy, lintegral_union measurableSet_Ioo]
  rw [Set.disjoint_iff]
  rintro x ⟨h1 : x ≤ _, h2, _⟩
  linarith

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

  have leftmid : ∫⁻ x in Iio 1, betaPDF a b x =
  ∫⁻ x in Ioo 0 1, ENNReal.ofReal (1 / (Beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1)) := by
    have expand : ∫⁻ x in Iio 1, betaPDF a b x =
    (∫⁻ x in Iic 0, betaPDF a b x) + (∫⁻ x in Ioo 0 1, betaPDF a b x) := by
      apply lintegral_Iio_eq_lintegral_Iic_add_Ioo (betaPDF a b)
      apply zero_lt_one
    rw [expand, left, middle, zero_add]

  rw [← lintegral_add_compl _ measurableSet_Ici, compl_Ici,
    leftmid, right, zero_add]
  rw [← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae]

  · simp_rw [← integral_Ioc_eq_integral_Ioo, mul_assoc]
    rw [integral_mul_left]
    rw [← betaReal_Integral ha hb]
    ring_nf
    apply DivisionRing.mul_inv_cancel
    have h_betapos := beta_pos ha hb
    positivity
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
    exact ae_of_all _ (fun x (hx : 0 < x ∧ x < 1) ↦ by
      rw [Pi.zero_apply]
      have hpos := betaPDFReal_nonneg ha hb
      unfold betaPDFReal at hpos
      specialize hpos x
      rw [if_pos hx] at hpos
      exact hpos
    )
  · apply (measurable_betaPDFReal a b).aestronglyMeasurable.congr
    refine (ae_restrict_iff' measurableSet_Ioo).mpr <| ae_of_all _ fun x (hx : 0 < x ∧ x < 1) ↦ ?_
    simp_rw [betaPDFReal, eq_true_intro hx, ite_true]
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
  · exact ae_of_all _ fun b ↦ by simp only [Pi.zero_apply, betaPDFReal_nonneg ha hb]
  · exact (measurable_betaPDFReal a b).aestronglyMeasurable.restrict

lemma betaCDFReal_eq_lintegral {a b : ℝ} (ha : 0 < a) (hb: 0 < b) (x : ℝ) :
    betaCDFReal a b x = ENNReal.toReal (∫⁻ x in Iic x, betaPDF a b x) := by
  have : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  simp only [betaPDF, betaCDFReal, cdf_eq_toReal]
  simp only [betaMeasure, measurableSet_Iic, withDensity_apply, betaPDF]

end BetaCDF

end ProbabilityTheory
