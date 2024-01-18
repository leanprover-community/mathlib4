/-
Copyright (c) 2023 Claus Clausen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claus Clausen, Patrick Massot
-/
import Mathlib.Probability.Notation
import Mathlib.Probability.Cdf
import Mathlib.Probability.Distributions.Gamma

/-! # Exponential distributions over ℝ

Define the Exponential measure over the reals.

## Main definitions
* `exponentialPdfReal`: the function `r x ↦ r * exp (-(r * x)` for `0 ≤ x`
  or `0` else, which is the probability density function of a exponential distribution with
  rate `r` (when `hr : 0 < r`).
* `exponentialPdf`: `ℝ≥0∞`-valued pdf,
  `exponentialPdf r = ENNReal.ofReal (exponentialPdfReal r)`.
* `expMeasure`: an exponential measure on `ℝ`, parametrized by its rate `r`.
* `exponentialCdfReal`: the Cdf given by the definition of CDF in `ProbabilityTheory.Cdf` applied to
  the exponential measure.

## Main results
* `exponentialCdfReal_eq`: Proof that the `exponentialCdfReal` given by the definition equals the
  known function given as `r x ↦ 1 - exp (- (r * x))` for `0 ≤ x` or `0` else.
-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section ExponentialPdf

/-- The pdf of the exponential distribution depending on its rate -/
noncomputable
def exponentialPdfReal (r x : ℝ) : ℝ :=
  gammaPdfReal 1 r x

/-- The pdf of the exponential distribution, as a function valued in `ℝ≥0∞` -/
noncomputable
def exponentialPdf (r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (exponentialPdfReal r x)

lemma exponentialPdf_eq (r x : ℝ) :
    exponentialPdf r x = ENNReal.ofReal (if 0 ≤ x then r * exp (-(r * x)) else 0) := by
  rw [exponentialPdf, exponentialPdfReal, gammaPdfReal]
  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]

lemma exponentialPdf_of_neg {r x : ℝ} (hx : x < 0) : exponentialPdf r x = 0 := gammaPdf_of_neg hx

lemma exponentialPdf_of_nonneg {r x : ℝ} (hx : 0 ≤ x) :
    exponentialPdf r x = ENNReal.ofReal (r * rexp (-(r * x))) := by
  simp only [exponentialPdf_eq, if_pos hx]

/-- The Lebesgue integral of the exponential pdf over nonpositive reals equals 0-/
lemma lintegral_exponentialPdf_of_nonpos {x r : ℝ} (hx : x ≤ 0) :
    ∫⁻ y in Iio x, exponentialPdf r y = 0 := lintegral_gammaPdf_of_nonpos hx

/-- The exponential pdf is measurable. -/
@[measurability]
lemma measurable_exponentialPdfReal (r : ℝ) : Measurable (exponentialPdfReal r) :=
  measurable_gammaPdfReal 1 r

-- The exponential pdf is strongly measurable -/
@[measurability]
 lemma stronglyMeasurable_exponentialPdfReal (r : ℝ) :
     StronglyMeasurable (exponentialPdfReal r) := stronglyMeasurable_gammaPdfReal 1 r

/-- The exponential pdf is positive for all positive reals -/
lemma exponentialPdfReal_pos {x r : ℝ} (hr : 0 < r) (hx : 0 < x) :
    0 < exponentialPdfReal r x := gammaPdfReal_pos zero_lt_one hr hx

/-- The exponential pdf is nonnegative-/
lemma exponentialPdfReal_nonneg {r : ℝ} (hr : 0 < r) (x : ℝ) :
    0 ≤ exponentialPdfReal r x := gammaPdfReal_nonneg zero_lt_one hr x

open Measure

/-- The pdf of the exponential distribution integrates to 1 -/
@[simp]
lemma lintegral_exponentialPdf_eq_one {r : ℝ} (hr : 0 < r) : ∫⁻ x, exponentialPdf r x = 1 :=
  lintegral_gammaPdf_eq_one zero_lt_one hr

end ExponentialPdf

open MeasureTheory

/-- Measure defined by the exponential distribution -/
noncomputable
def expMeasure (r : ℝ) : Measure ℝ := gammaMeasure 1 r

lemma isProbabilityMeasureExponential {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (expMeasure r) := isProbabilityMeasureGamma zero_lt_one hr

section ExponentialCdf

/-- CDF of the exponential distribution -/
noncomputable
def exponentialCdfReal (r : ℝ) : StieltjesFunction :=
  cdf (expMeasure r)

lemma exponentialCdfReal_eq_integral {r : ℝ} (hr : 0 < r) (x : ℝ) :
    exponentialCdfReal r x = ∫ x in Iic x, exponentialPdfReal r x :=
  gammaCdfReal_eq_integral zero_lt_one hr x

lemma exponentialCdfReal_eq_lintegral {r : ℝ} (hr : 0 < r) (x : ℝ) :
    exponentialCdfReal r x = ENNReal.toReal (∫⁻ x in Iic x, exponentialPdf r x) :=
  gammaCdfReal_eq_lintegral zero_lt_one hr x

open Topology

lemma hasDerivAt_neg_exp_mul_exp {r x : ℝ} :
    HasDerivAt (fun a ↦ -exp (-(r * a))) (r * exp (-(r * x))) x := by
  convert (((hasDerivAt_id x).const_mul (-r)).exp.const_mul (-1)) using 1
  · simp only [one_mul, id_eq, neg_mul]
  simp only [id_eq, neg_mul, mul_one, mul_neg, one_mul, neg_neg, mul_comm]

/-- A negative exponential function is integrable on intervals in `R≥0` -/
lemma exp_neg_integrableOn_Ioc {b x : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x ↦ rexp (-(b * x))) (Ioc 0 x) := by
  simp only [neg_mul_eq_neg_mul]
  exact (exp_neg_integrableOn_Ioi _ hb).mono_set Ioc_subset_Ioi_self

lemma lintegral_exponentialPdf_eq_antiDeriv {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ∫⁻ y in Iic x, exponentialPdf r y
    = ENNReal.ofReal (if 0 ≤ x then 1 - exp (-(r * x)) else 0) := by
  split_ifs with h
  case neg =>
    simp only [exponentialPdf_eq]
    rw [set_lintegral_congr_fun measurableSet_Iic, lintegral_zero, ENNReal.ofReal_zero]
    exact ae_of_all _ fun a (_ : a ≤ _) ↦ by rw [if_neg (by linarith), ENNReal.ofReal_eq_zero]
  case pos =>
    rw [lintegral_Iic_eq_lintegral_Iio_add_Icc _ h, lintegral_exponentialPdf_of_nonpos (le_refl 0),
      zero_add]
    simp only [exponentialPdf_eq]
    rw [set_lintegral_congr_fun measurableSet_Icc (ae_of_all _
        (by intro a ⟨(hle : _ ≤ a), _⟩; rw [if_pos hle]))]
    rw [← ENNReal.toReal_eq_toReal _ ENNReal.ofReal_ne_top, ← integral_eq_lintegral_of_nonneg_ae
        (eventually_of_forall fun _ ↦ le_of_lt (mul_pos hr (exp_pos _)))]
    have : ∫ a in uIoc 0 x, r * rexp (-(r * a)) = ∫ a in (0)..x, r * rexp (-(r * a)) := by
      rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul, if_pos h, one_mul]
    rw [integral_Icc_eq_integral_Ioc, ← uIoc_of_le h, this]
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h
      (f := fun a ↦ -1 * rexp (-(r * a))) _ _]
    rw [ENNReal.toReal_ofReal_eq_iff.2 (by norm_num; positivity)]
    · norm_num; ring
    · simp only [intervalIntegrable_iff, uIoc_of_le h]
      exact Integrable.const_mul (exp_neg_integrableOn_Ioc hr) _
    · have : Continuous (fun a ↦ rexp (-(r * a))) := by
        simp only [← neg_mul]; exact (continuous_mul_left (-r)).exp
      exact Continuous.continuousOn (Continuous.comp' (continuous_mul_left (-1)) this)
    · simp only [neg_mul, one_mul]
      exact fun _ _ ↦ HasDerivAt.hasDerivWithinAt hasDerivAt_neg_exp_mul_exp
    · apply Integrable.aestronglyMeasurable (Integrable.const_mul _ _)
      rw [← integrableOn_def, integrableOn_Icc_iff_integrableOn_Ioc]
      exact exp_neg_integrableOn_Ioc hr
    · refine ne_of_lt (IntegrableOn.set_lintegral_lt_top ?_)
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact Integrable.const_mul (exp_neg_integrableOn_Ioc hr) _

/-- The CDF of the exponential distribution equals ``1 - exp (-(r * x))``-/
lemma exponentialCdfReal_eq {r : ℝ} (hr : 0 < r) (x : ℝ) :
    exponentialCdfReal r x = if 0 ≤ x then 1 - exp (-(r * x)) else 0 := by
  rw [exponentialCdfReal_eq_lintegral hr, lintegral_exponentialPdf_eq_antiDeriv hr x,
    ENNReal.toReal_ofReal_eq_iff]
  split_ifs with h
  · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff, gt_iff_lt, ge_iff_le]
    exact mul_nonneg hr.le h
  · exact le_rfl

end ExponentialCdf
