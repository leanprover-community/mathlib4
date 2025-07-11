/-
Copyright (c) 2023 Claus Clausen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claus Clausen, Patrick Massot
-/
import Mathlib.Probability.Notation
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gamma

/-! # Exponential distributions over ℝ

Define the Exponential measure over the reals.

## Main definitions
* `exponentialPDFReal`: the function `r x ↦ r * exp (-(r * x)` for `0 ≤ x`
  or `0` else, which is the probability density function of a exponential distribution with
  rate `r` (when `hr : 0 < r`).
* `exponentialPDF`: `ℝ≥0∞`-valued pdf,
  `exponentialPDF r = ENNReal.ofReal (exponentialPDFReal r)`.
* `expMeasure`: an exponential measure on `ℝ`, parametrized by its rate `r`.
* `exponentialCDFReal`: the CDF given by the definition of CDF in `ProbabilityTheory.CDF` applied to
  the exponential measure.

## Main results
* `exponentialCDFReal_eq`: Proof that the `exponentialCDFReal` given by the definition equals the
  known function given as `r x ↦ 1 - exp (- (r * x))` for `0 ≤ x` or `0` else.
-/

open scoped ENNReal NNReal

open MeasureTheory Real Set Filter Topology

namespace ProbabilityTheory

section ExponentialPDF

/-- The pdf of the exponential distribution depending on its rate -/
noncomputable
def exponentialPDFReal (r x : ℝ) : ℝ :=
  gammaPDFReal 1 r x

/-- The pdf of the exponential distribution, as a function valued in `ℝ≥0∞` -/
noncomputable
def exponentialPDF (r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (exponentialPDFReal r x)

lemma exponentialPDF_eq (r x : ℝ) :
    exponentialPDF r x = ENNReal.ofReal (if 0 ≤ x then r * exp (-(r * x)) else 0) := by
  rw [exponentialPDF, exponentialPDFReal, gammaPDFReal]
  simp only [rpow_one, Gamma_one, div_one, sub_self, rpow_zero, mul_one]

lemma exponentialPDF_of_neg {r x : ℝ} (hx : x < 0) : exponentialPDF r x = 0 := gammaPDF_of_neg hx

lemma exponentialPDF_of_nonneg {r x : ℝ} (hx : 0 ≤ x) :
    exponentialPDF r x = ENNReal.ofReal (r * rexp (-(r * x))) := by
  simp only [exponentialPDF_eq, if_pos hx]

/-- The Lebesgue integral of the exponential pdf over nonpositive reals equals 0 -/
lemma lintegral_exponentialPDF_of_nonpos {x r : ℝ} (hx : x ≤ 0) :
    ∫⁻ y in Iio x, exponentialPDF r y = 0 := lintegral_gammaPDF_of_nonpos hx

/-- The exponential pdf is measurable. -/
@[fun_prop, measurability]
lemma measurable_exponentialPDFReal (r : ℝ) : Measurable (exponentialPDFReal r) :=
  measurable_gammaPDFReal 1 r

-- The exponential pdf is strongly measurable -/
@[fun_prop, measurability]
lemma stronglyMeasurable_exponentialPDFReal (r : ℝ) :
    StronglyMeasurable (exponentialPDFReal r) := stronglyMeasurable_gammaPDFReal 1 r

/-- The exponential pdf is positive for all positive reals -/
lemma exponentialPDFReal_pos {x r : ℝ} (hr : 0 < r) (hx : 0 < x) :
    0 < exponentialPDFReal r x := gammaPDFReal_pos zero_lt_one hr hx

/-- The exponential pdf is nonnegative -/
lemma exponentialPDFReal_nonneg {r : ℝ} (hr : 0 < r) (x : ℝ) :
    0 ≤ exponentialPDFReal r x := gammaPDFReal_nonneg zero_lt_one hr x

open Measure

/-- The pdf of the exponential distribution integrates to 1 -/
@[simp]
lemma lintegral_exponentialPDF_eq_one {r : ℝ} (hr : 0 < r) : ∫⁻ x, exponentialPDF r x = 1 :=
  lintegral_gammaPDF_eq_one zero_lt_one hr

end ExponentialPDF

open MeasureTheory

/-- Measure defined by the exponential distribution -/
noncomputable
def expMeasure (r : ℝ) : Measure ℝ := gammaMeasure 1 r

lemma isProbabilityMeasureExponential {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (expMeasure r) := isProbabilityMeasureGamma zero_lt_one hr

section ExponentialCDF

/-- CDF of the exponential distribution -/
noncomputable
def exponentialCDFReal (r : ℝ) : StieltjesFunction :=
  cdf (expMeasure r)

lemma exponentialCDFReal_eq_integral {r : ℝ} (hr : 0 < r) (x : ℝ) :
    exponentialCDFReal r x = ∫ x in Iic x, exponentialPDFReal r x :=
  gammaCDFReal_eq_integral zero_lt_one hr x

lemma exponentialCDFReal_eq_lintegral {r : ℝ} (hr : 0 < r) (x : ℝ) :
    exponentialCDFReal r x = ENNReal.toReal (∫⁻ x in Iic x, exponentialPDF r x) :=
  gammaCDFReal_eq_lintegral zero_lt_one hr x

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

lemma lintegral_exponentialPDF_eq_antiDeriv {r : ℝ} (hr : 0 < r) (x : ℝ) :
    ∫⁻ y in Iic x, exponentialPDF r y
    = ENNReal.ofReal (if 0 ≤ x then 1 - exp (-(r * x)) else 0) := by
  split_ifs with h
  case neg =>
    simp only [exponentialPDF_eq]
    rw [setLIntegral_congr_fun measurableSet_Iic, lintegral_zero, ENNReal.ofReal_zero]
    exact fun a (_ : a ≤ _) ↦ by rw [if_neg (by linarith), ENNReal.ofReal_eq_zero]
  case pos =>
    rw [lintegral_Iic_eq_lintegral_Iio_add_Icc _ h, lintegral_exponentialPDF_of_nonpos (le_refl 0),
      zero_add]
    simp only [exponentialPDF_eq]
    rw [setLIntegral_congr_fun measurableSet_Icc (g := fun x ↦ ENNReal.ofReal (r * rexp (-(r * x))))
      (by intro a ha; simp [ha.1])]
    rw [← ENNReal.toReal_eq_toReal _ ENNReal.ofReal_ne_top, ← integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun _ ↦ le_of_lt (mul_pos hr (exp_pos _)))]
    · have : ∫ a in uIoc 0 x, r * rexp (-(r * a)) = ∫ a in (0)..x, r * rexp (-(r * a)) := by
        rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, smul_eq_mul, if_pos h, one_mul]
      rw [integral_Icc_eq_integral_Ioc, ← uIoc_of_le h, this]
      rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h
        (f := fun a ↦ -1 * rexp (-(r * a))) _ _]
      · rw [ENNReal.toReal_ofReal_eq_iff.2 (by norm_num; positivity)]
        norm_num; ring
      · simp only [intervalIntegrable_iff, uIoc_of_le h]
        exact Integrable.const_mul (exp_neg_integrableOn_Ioc hr) _
      · have : Continuous (fun a ↦ rexp (-(r * a))) := by
          simp only [← neg_mul]; exact (continuous_mul_left (-r)).rexp
        exact Continuous.continuousOn (Continuous.comp' (continuous_mul_left (-1)) this)
      · simp only [neg_mul, one_mul]
        exact fun _ _ ↦ HasDerivAt.hasDerivWithinAt hasDerivAt_neg_exp_mul_exp
    · refine Integrable.aestronglyMeasurable (Integrable.const_mul ?_ _)
      rw [← IntegrableOn, integrableOn_Icc_iff_integrableOn_Ioc]
      exact exp_neg_integrableOn_Ioc hr
    · refine ne_of_lt (IntegrableOn.setLIntegral_lt_top ?_)
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact Integrable.const_mul (exp_neg_integrableOn_Ioc hr) _

/-- The CDF of the exponential distribution equals ``1 - exp (-(r * x))`` -/
lemma exponentialCDFReal_eq {r : ℝ} (hr : 0 < r) (x : ℝ) :
    exponentialCDFReal r x = if 0 ≤ x then 1 - exp (-(r * x)) else 0 := by
  rw [exponentialCDFReal_eq_lintegral hr, lintegral_exponentialPDF_eq_antiDeriv hr x,
    ENNReal.toReal_ofReal_eq_iff]
  split_ifs with h
  · simp only [sub_nonneg, exp_le_one_iff, Left.neg_nonpos_iff]
    exact mul_nonneg hr.le h
  · exact le_rfl

end ExponentialCDF

end ProbabilityTheory
