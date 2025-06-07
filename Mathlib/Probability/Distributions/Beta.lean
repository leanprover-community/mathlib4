/-
Copyright (c) 2024 Alvan Caleb Arulandu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alvan Caleb Arulandu
-/
import Mathlib.Probability.Notation
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Beta distributions over ℝ

Define the Beta measure over the reals.

## Main definitions
* `betaPDFReal`: the function `a b x ↦ 1 / (betaIntegral a b) * x ^ (a - 1) * (1 - x) ^ (b - 1)`
  for `0 ≤ x` or `0` else, which is the probability density function of a Beta distribution with
  shape parameters `a` and `b` (when `ha : 0 < a ` and `hb: 0 < b`).
* `betaPDF`: `ℝ≥0∞`-valued pdf,
  `betaPDF a b = ENNReal.ofReal (betaPDFReal a b)`.
* `betaMeasure`: a Beta measure on `ℝ`, parametrized by its shape parameters `a` and `b`.
* `betaCDFReal`: the CDF given by the definition of CDF in `ProbabilityTheory.CDF` applied to the
  Beta measure.
-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section BetaPDF

/-- The pdf of the Beta distribution depending on its scale and rate. -/
noncomputable def betaPDFReal (a b x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then 1 / (Beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1) else 0

/-- The pdf of the Beta distribution, as a function valued in `ℝ≥0∞` -/
noncomputable def betaPDF (a b x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (betaPDFReal a b x)

lemma betaPDF_eq (a b x : ℝ) :
    betaPDF a b x = ENNReal.ofReal (if 0 < x ∧ x < 1
    then 1 / (Beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1) else 0) := rfl

-- TODO: if a,b <= 0, result holds by the integrand vanishing.
lemma betaPDFReal_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) : 0 ≤ betaPDFReal a b x := by
  unfold betaPDFReal
  split_ifs with ht
  · have h1 : x ^ (a - 1) ≥ 0 := rpow_nonneg (le_of_lt ht.left) (a - 1)
    have h2 : (1 - x) ^ (b - 1) ≥ 0 := by
      have hp : 1 - x ≥ 0 := by linarith
      exact rpow_nonneg hp (b - 1)
    have hbeta:= Beta_pos ha hb
    positivity
  trivial

lemma betaPDF_of_nonpos_or_one_le {a b x : ℝ} (hx : x <= 0 ∨ 1 ≤ x) : betaPDF a b x = 0 := by
  rw [betaPDF_eq]
  have hx_n : ¬(0 < x ∧ x < 1) := by
    simp only [not_and_or, not_lt]
    exact hx
  rw [if_neg hx_n, ENNReal.ofReal_zero]

lemma betaPDF_of_nonpos {a b x : ℝ} (hx : x <= 0) : betaPDF a b x = 0 :=
betaPDF_of_nonpos_or_one_le (Or.inl hx)

lemma betaPDF_of_one_le {a b x : ℝ} (hx : 1 ≤ x) : betaPDF a b x = 0 :=
betaPDF_of_nonpos_or_one_le (Or.inr hx)

lemma betaPDF_of_pos_lt_one {a b x : ℝ} (hx : 0 < x ∧ x < 1) :
    betaPDF a b x = ENNReal.ofReal (1 / (Beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1)) := by
  simp only [betaPDF_eq, if_pos hx]

/-- The Lebesgue integral of the Beta pdf over nonpositive reals equals 0. -/
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

lemma lintegral_betaPDF_of_one_le {x a b : ℝ} (hx : 1 ≤ x) :
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

/-- The Beta pdf is measurable. -/
@[measurability, fun_prop]
lemma measurable_betaPDFReal (a b : ℝ) : Measurable (betaPDFReal a b) :=
  Measurable.ite
    measurableSet_Ioo (((measurable_id'.pow_const _).const_mul _).mul
    ((measurable_const.sub' measurable_id').pow_const _))
    measurable_const

/-- The Beta pdf is strongly measurable. -/
@[measurability]
 lemma stronglyMeasurable_betaPDFReal (a b : ℝ) :
     StronglyMeasurable (betaPDFReal a b) :=
   (measurable_betaPDFReal a b).stronglyMeasurable

open Measure

/-- A Lebesgue Integral from -∞ to y can be expressed as the sum of one from -∞ to 0 and 0 to x. -/
lemma lintegral_Iio_eq_lintegral_Iic_add_Ioo {y z : ℝ} (f : ℝ → ℝ≥0∞) (hzy : z < y) :
    ∫⁻ x in Iio y, f x = (∫⁻ x in Iic z, f x) + ∫⁻ x in Ioo z y, f x := by
  rw [← Iic_union_Ioo_eq_Iio hzy, lintegral_union measurableSet_Ioo]
  rw [Set.disjoint_iff]
  rintro x ⟨h1 : x ≤ _, h2, _⟩
  linarith

/-- The pdf of the Beta distribution integrates to 1. -/
@[simp]
lemma lintegral_betaPDF_eq_one {a b : ℝ} (ha : 0 < a) (hb: 0 < b) :
    ∫⁻ x, betaPDF a b x = 1 := by
  have left : ∫⁻ x in Iic 0, betaPDF a b x = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Iic
      (ae_of_all _ (fun x (hx : x ≤ 0) ↦ betaPDF_of_nonpos hx)), lintegral_zero]
  have middle : ∫⁻ x in Ioo 0 1, betaPDF a b x =
      ∫⁻ x in Ioo 0 1, ENNReal.ofReal (1 / (Beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1)) :=
    setLIntegral_congr_fun measurableSet_Ioo (ae_of_all _ (fun _ ↦ betaPDF_of_pos_lt_one))
  have right : ∫⁻ x in Ici 1, betaPDF a b x = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ici
      (ae_of_all _ (fun x (hx : x ≥ 1) ↦ betaPDF_of_one_le hx)), lintegral_zero]
  have leftmid : ∫⁻ x in Iio 1, betaPDF a b x =
  ∫⁻ x in Ioo 0 1, ENNReal.ofReal (1 / (Beta a b) * x ^ (a - 1) * (1 - x) ^ (b - 1)) := by
    rw [lintegral_Iio_eq_lintegral_Iic_add_Ioo _ zero_lt_one, left, middle, zero_add]
  rw [← lintegral_add_compl _ measurableSet_Ici, compl_Ici,
    leftmid, right, zero_add]
  rw [← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae]
  · simp_rw [mul_assoc]
    rw [integral_mul_left, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one, ← BetaIntegral_ofReal ha hb,
    one_div_mul_cancel (Beta_pos ha hb).ne']
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioo]
    refine ae_of_all _ fun x hx ↦ ?_
    convert betaPDFReal_nonneg ha hb x using 1
    rw [betaPDFReal, if_pos (mem_Ioo.1 hx)]
  · apply (measurable_betaPDFReal a b).aestronglyMeasurable.congr
    refine (ae_restrict_iff' measurableSet_Ioo).mpr <| ae_of_all _ fun x (hx : 0 < x ∧ x < 1) ↦ ?_
    simp_rw [betaPDFReal, eq_true_intro hx, ite_true]

end BetaPDF

open MeasureTheory

/-- Measure defined by the Beta distribution. -/
noncomputable def betaMeasure (a b : ℝ) : Measure ℝ :=
  volume.withDensity (betaPDF a b)

lemma isProbabilityMeasureBeta {a b : ℝ} (ha : 0 < a) (hb: 0 < b) :
    IsProbabilityMeasure (betaMeasure a b) where
  measure_univ := by simp [betaMeasure, lintegral_betaPDF_eq_one ha hb]

section BetaCDF

/-- CDF of the Beta distribution. -/
noncomputable def betaCDFReal (a b : ℝ) : StieltjesFunction :=
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
