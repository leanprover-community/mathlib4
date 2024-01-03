/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Probability.Notation
import Mathlib.Probability.Cdf

/-! # Gamma distributions over ℝ

Define the Gamma Measure over the Reals

## Main definitions
* `gammaPdfReal`: the function `a r x ↦ r^a/(Real.Gamma a) * (↑x)^(a-1) * Real.exp (-(r * ↑x))`
  for `0 ≤ x` or `0` else, which is the probability density function of a Gamma distribution with
  shape `a` and rate `r` (when `ha : 0 < a ` and `hr : 0 < r`).
* `gammaPdf`: `ℝ≥0∞`-valued pdf,
  `gammaPdf a r = ENNReal.ofReal (gammaPdfReal a r)`.
* `gammaMeasure`: a Gamma measure on `ℝ`, parametrized by its shape `a` and rate `r`.
* `gammaCdfReal`: the Cdf given by the Definition of CDF in `ProbabilityTheory.Cdf` on

## Main results
* `gammaCdfReal_eq`: Proof that the `gammaCdfReal` given by the Definition equals the
  known function given as `a r x ↦ r^a/(Real.Gamma a) * (↑x)^(a-1) * Real.exp (-(r * ↑x))` for
  `0 ≤ x` or `0` else.

## TODO: Refactoring notes
* To refactor Exponential.lean using the resuls in this file:
* - `lintegral_Iic_eq_lintegral_Iio_add_Icc` and `lintegral_eq_lintegral_Ici_add_Iio` are repeated
    in this file, as this file should precede Exponential.lean after refactoring. Remove these
    functions from there.
-/

open scoped ENNReal NNReal Real

open MeasureTheory Real Set Filter Topology

/-- A Lebesgue Integral from -∞ to y can be expressed as the sum of one from -∞ to 0 and 0 to x -/
lemma lintegral_Iic_eq_lintegral_Iio_add_Icc {y z : ℝ} (f : ℝ → ℝ≥0∞) (hzy : z ≤ y) :
    ∫⁻ x in Iic y, f x = (∫⁻ x in Iio z, f x) + ∫⁻ x in Icc z y, f x := by
  rw [← Iio_union_Icc_eq_Iic hzy, lintegral_union measurableSet_Icc]
  rw [Set.disjoint_iff]
  rintro x ⟨h1 : x < _, h2, _⟩
  linarith

lemma lintegral_eq_lintegral_Ici_add_Iio (f : ℝ → ℝ≥0∞) (c : ℝ) :
    ∫⁻ x, f x = (∫⁻ x in Ici c, f x) + ∫⁻ x in Iio c, f x := by
  have union : univ = {x : ℝ | x ≥ c} ∪ {x : ℝ | x < c} := by
    ext x; simp [le_or_lt]
  calc
  ∫⁻ x, f x = ∫⁻ x in univ, f x ∂volume := (set_lintegral_univ f).symm
  _ = ∫⁻ x in {x | x ≥ c} ∪ {x | x < c} , f x ∂volume := by rw [← union]
  _ = _ := by
    apply lintegral_union (isOpen_gt' c).measurableSet
    rw [Set.disjoint_iff]
    rintro x ⟨hxge : x ≥ _, hxlt : x < _⟩
    linarith

namespace ProbabilityTheory

section GammaPdf

/-- Define the PDF of the gamma distribution depending on its scale and rate-/
noncomputable
def gammaPdfReal (a r x : ℝ) : ℝ :=
  if 0 ≤ x then r^a/(Real.Gamma a) * (↑x)^(a-1) * Real.exp (-(r * ↑x)) else 0

/-- The PDF of the gamma Distribution on the extended real Numbers-/
noncomputable
def gammaPdf (a r x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (gammaPdfReal a r x)

lemma gammaPdf_eq (a r x : ℝ) :
    gammaPdf a r x = ENNReal.ofReal (if 0 ≤ x then
    r^a/(Real.Gamma a) * (↑x)^(a-1) * Real.exp (-(r * ↑x)) else 0) := rfl

lemma gammaPdf_of_neg {a r x : ℝ} (hx : x < 0) : gammaPdf a r x = 0 := by
  simp only [gammaPdf_eq, if_neg (not_le.mpr hx), ENNReal.ofReal_zero]

lemma gammaPdf_of_nonneg {a r x : ℝ} (hx : 0 ≤ x) :
    gammaPdf a r x = ENNReal.ofReal (r^a/(Real.Gamma a) * (↑x)^(a-1) * Real.exp (-(r * ↑x))) := by
  simp only [gammaPdf_eq, if_pos hx]

/-- the Lebesgue-Integral of the gamma PDF over nonpositive Reals equals 0-/
lemma lintegral_gammaPdf_of_nonpos {x a r : ℝ} (hx : x ≤ 0) :
    ∫⁻ y in Iio x, gammaPdf a r y = 0 := by
  rw [set_lintegral_congr_fun (g := fun _ ↦ 0) measurableSet_Iio]
  · rw [lintegral_zero, ← ENNReal.ofReal_zero]
  · simp only [gammaPdf_eq, ge_iff_le, ENNReal.ofReal_eq_zero]
    apply ae_of_all _ fun a (_ : a < _) ↦ by rw [if_neg (by linarith)]

/-- The gamma pdf is measurable. -/
lemma measurable_gammaPdfReal (a r : ℝ) :
    Measurable (gammaPdfReal a r) := by
  unfold gammaPdfReal
  refine Measurable.ite ?hp ?hf ?hg
  · exact measurableSet_Ici
  · exact ((measurable_id'.pow_const (a-1)).const_mul (r^a/Real.Gamma a)).mul
     (measurable_id'.const_mul r).neg.exp
  · exact measurable_const

/-- The gamma Pdf is strongly measurable -/
lemma stronglyMeasurable_gammaPdfReal (a r : ℝ) :
    StronglyMeasurable (gammaPdfReal a r) :=
  (measurable_gammaPdfReal a r).stronglyMeasurable

/-- the gamma Pdf is positive for all positive reals-/
lemma gammaPdfReal_pos {x a r : ℝ} {ha : 0 < a} {hr : 0 < r} (hx : 0 < x) :
    0 < gammaPdfReal a r x := by
  simp only [gammaPdfReal, if_pos hx.le]
  positivity

/-- The gamma Pdf is nonnegative-/
lemma gammaPdfReal_nonneg {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    0 ≤ gammaPdfReal a r x := by
  unfold gammaPdfReal; split_ifs <;> positivity

/-- Expresses the integral over Ioi 0 of t^(a-1) * exp(-r*t) in terms of the Gamma function. -/
lemma pow_exp_integral_Ioi {a r : ℝ} (ha : a > 0) (hr : r > 0) :
    ∫ (t : ℝ) in Ioi 0, t ^ (a - 1) * rexp (-(r * t))
    = (1/r)^a * Gamma (a) := by
  have hri : 0 < 1/r := by positivity
  calc ∫ (t : ℝ) in Ioi 0, t ^ (a - 1) * rexp (-(r * t))
    _ = ∫ (t : ℝ) in Ioi 0, (1/r)^(a-1) * (r * t) ^ (a - 1) * rexp (-(r * t)) := by
      apply MeasureTheory.set_integral_congr
      · simp
      · intro x hx
        have hx : 0 < x := hx
        simp only [smul_eq_mul, mul_eq_mul_right_iff]
        apply Or.inl
        rw [mul_rpow hr.le hx.le, ← mul_assoc, ← mul_rpow hri.le hr.le]
        rw [mul_comm (1/r) r, mul_div, mul_one, div_self hr.ne']
        simp
    _ =  |1/r| * ∫ (t : ℝ) in Ioi (r * 0), (1/r)^(a-1) * t ^ (a - 1) * rexp (-t) := by
      rw [integral_comp_mul_left_Ioi (fun t ↦ (1/r)^(a-1) * (t) ^ (a - 1) * rexp (-t)) (0 : ℝ) hr]
      simp
    _ =  1/r * ∫ (t : ℝ) in Ioi 0, (1/r)^(a-1) • t ^ (a - 1) * rexp (-t) := by
      have : Ioi (r * 0) = Ioi 0 := by refine Ioi_inj.mpr (by simp)
      rw [this, abs_of_nonneg hri.le]
      rfl
    _ =  1/r * ∫ (t : ℝ) in Ioi 0, (1/r)^(a-1) • (t ^ (a - 1) * rexp (-t)) := by
      congr
      ext x
      exact smul_mul_assoc _ _ _
    _ =  1/r * (1/r)^(a-1) • (∫ (t : ℝ) in Ioi 0, t ^ (a - 1) * rexp (-t)) := by
      rw [integral_smul]
    _ = (1/r)^a • (∫ (t : ℝ) in Ioi 0, t ^ (a - 1) * rexp (-t)) := by
      have : (1/r)^a = 1/r * (1/r)^(a-1) := by
        nth_rewrite 2 [← rpow_one (1/r)]
        rw [← rpow_add]
        simp only [one_div, add_sub_cancel'_right]
        exact hri
      rw [this, smul_eq_mul, smul_eq_mul, mul_assoc]
    _ = (1/r)^a * Gamma (a) := by
      rw [Gamma_eq_integral]
      congr
      ext x
      group
      exact ha

/-- Expresses the integral over Ioi 0 of t^(a-1) * exp(-r*t) in terms of the Gamma function. -/
lemma pow_exp_integral_Ioi_insert_1 {a r : ℝ} (ha : a > 0) (hr : r > 0) :
    ∫ (t : ℝ) in Ioi 0, (r ^ a / Gamma a) * t ^ (a - 1) * rexp (-(r * t))
    = 1 := by
  calc ∫ (t : ℝ) in Ioi 0, (r ^ a / Gamma a) * t ^ (a - 1) * rexp (-(r * t))
  _ = ∫ (t : ℝ) in Ioi 0, (r ^ a / Gamma a) • (t ^ (a - 1) * rexp (-(r * t))) := by
    congr
    ext x
    rw [smul_eq_mul, mul_assoc]
  _ = (r ^ a / Gamma a) • ∫ (t : ℝ) in Ioi 0, t ^ (a - 1) * rexp (-(r * t)) := by
    apply integral_smul
  _ = (r ^ a / Gamma a) * (1/r)^a * Gamma (a) := by
    rw [pow_exp_integral_Ioi ha hr, smul_eq_mul, mul_assoc]
  _ = 1 := by
    rw [mul_assoc, div_mul_eq_mul_div, ← mul_assoc]
    have : r^a * (1/r)^a = 1 := by
      have : 0 ≤ 1/r := by positivity
      rw [← mul_rpow hr.le this, mul_div, mul_comm, mul_div_assoc, div_self hr.ne']
      simp
    rw [this]
    have : Gamma a / Gamma a = 1 := div_self (Gamma_pos_of_pos ha).ne'
    simp [this]

open Measure

/-- The Pdf of the gamma Distribution integrates to 1-/
@[simp]
lemma lintegral_gammaPdf_eq_one (a r : ℝ) (ha : 0 < a) (hr : 0 < r) : ∫⁻ x, gammaPdf a r x = 1 := by
  rw [lintegral_eq_lintegral_Ici_add_Iio (gammaPdf a r) 0, ← ENNReal.toReal_eq_one_iff]
  have leftSide : ∫⁻ x in Iio 0, gammaPdf a r x = 0 := by
    rw [set_lintegral_congr_fun measurableSet_Iio
      (ae_of_all _ (fun x (hx : x < 0) ↦ gammaPdf_of_neg hx)), lintegral_zero]
  have rightSide :
      ∫⁻ x in Ici 0, gammaPdf a r x =
      ∫⁻ x in Ici 0, ENNReal.ofReal (r^a/(Real.Gamma a) * x^(a-1) * rexp (-(r * x))) :=
    set_lintegral_congr_fun isClosed_Ici.measurableSet
      (ae_of_all _ (fun x (hx : 0 ≤ x) ↦ gammaPdf_of_nonneg hx))
  simp only [leftSide, add_zero]
  rw [rightSide]
  rw [← integral_eq_lintegral_of_nonneg_ae]
  · rw [MeasureTheory.integral_Ici_eq_integral_Ioi, pow_exp_integral_Ioi_insert_1 ha hr]
  · unfold EventuallyLE
    simp only [Pi.zero_apply]
    rw [ae_restrict_iff]
    simp only [mem_Ici]
    · apply ae_of_all
      intro x hx
      positivity
    · refine measurableSet_le measurable_const ?_
      refine Measurable.mul ?_ ?_
      · measurability
      · apply (Measurable.neg ?_).exp
        exact measurable_id.const_mul _
  · have := (@MeasureTheory.restrict_Ioi_eq_restrict_Ici ℝ _ ℙ _ _ 0)
    rw [← this]
    apply ContinuousOn.aestronglyMeasurable _ (by measurability)
    apply ContinuousOn.mul
    · apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      apply Or.inl
      exact ne_of_gt hx
    · apply ContinuousOn.exp
      apply ContinuousOn.neg
      apply ContinuousOn.mul continuousOn_const continuousOn_id

end GammaPdf

open MeasureTheory

/-- Measure defined by the Gamma Distribution -/
noncomputable
def gammaMeasure (a r : ℝ) : Measure ℝ :=
  volume.withDensity (gammaPdf a r)

instance instIsProbabilityMeasureGamma (a r : ℝ) [Fact (0 < a)] [Fact (0 < r)] :
    IsProbabilityMeasure (gammaMeasure a r) where
  measure_univ := by simp [gammaMeasure, lintegral_gammaPdf_eq_one a r Fact.out Fact.out]

section GammaCdf

/-- CDF of the Gamma Distribution -/
noncomputable
def gammaCdfReal (a r : ℝ) : StieltjesFunction :=
  cdf (gammaMeasure a r)

lemma gammaCdfReal_eq_integral (a r x : ℝ) [Fact (0 < a)] [Fact (0 < r)] :
    gammaCdfReal a r x = ∫ x in Iic x, gammaPdfReal a r x := by
  rw [gammaCdfReal,cdf_eq_toReal]
  simp only [gammaMeasure, measurableSet_Iic, withDensity_apply]
  rw [integral_eq_lintegral_of_nonneg_ae]; exact rfl
  · exact ae_of_all _ fun b ↦ by simp [Pi.zero_apply, gammaPdfReal_nonneg Fact.out Fact.out]
  · exact (Measurable.aestronglyMeasurable (measurable_gammaPdfReal a r)).restrict

lemma gammaCdfReal_eq_lintegral (a r x : ℝ) [Fact (0 < a)] [Fact (0 < r)] :
    gammaCdfReal a r x = ENNReal.toReal (∫⁻ x in Iic x, gammaPdf a r x) := by
  simp only [gammaPdf, gammaCdfReal, cdf_eq_toReal]
  simp only [gammaMeasure, measurableSet_Iic, withDensity_apply, gammaPdf]

end GammaCdf
