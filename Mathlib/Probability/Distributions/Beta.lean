/-
Copyright (c) 2025 Tommy Löfgren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tommy Löfgren
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Beta distributions over ℝ

Define the beta distribution over the reals.

## Main definitions
* `betaPDFReal`: the function `α β x ↦ (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)`
  for `0 < x ∧ x < 1` or `0` else, which is the probability density function of a beta distribution
  with shape parameters `α` and `β` (when `0 < α` and `0 < β`).
* `betaPDF`: `ℝ≥0∞`-valued pdf,
  `betaPDF α β = ENNReal.ofReal (betaPDFReal α β)`.
-/

open scoped ENNReal NNReal

open MeasureTheory Complex Set

namespace ProbabilityTheory

section BetaPDF

/-- The normalizing constant in the beta distribution. -/
noncomputable def beta (α β : ℝ) : ℝ :=
  Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)

lemma beta_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : 0 < beta α β :=
  div_pos (mul_pos (Real.Gamma_pos_of_pos hα) (Real.Gamma_pos_of_pos hβ))
    (Real.Gamma_pos_of_pos (add_pos hα hβ))

/-- Relation between the beta function and the gamma function over the reals. -/
theorem beta_eq_betaIntegralReal (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    beta α β = (betaIntegral α β).re := by
  rw [betaIntegral_eq_Gamma_mul_div]
  · simp_rw [beta, ← ofReal_add α β, Gamma_ofReal]
    norm_cast
  all_goals simpa

/-- The probability density function of the beta distribution with shape parameters `α` and `β`.
    Returns `(1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)`
    when `0 < x < 1` and `0` otherwise. -/
noncomputable def betaPDFReal (α β x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then
    (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)
  else
    0

/-- The pdf of the beta distribution, as a function valued in `ℝ≥0∞`. -/
noncomputable def betaPDF (α β x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (betaPDFReal α β x)

lemma betaPDF_eq (α β x : ℝ) :
    betaPDF α β x =
      ENNReal.ofReal (if 0 < x ∧ x < 1 then
        (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1) else 0) := rfl

lemma betaPDF_eq_zero_of_nonpos {α β x : ℝ} (hx : x ≤ 0) :
    betaPDF α β x = 0 := by
  simp [betaPDF_eq, hx.not_gt]

lemma betaPDF_eq_zero_of_one_le {α β x : ℝ} (hx : 1 ≤ x) :
    betaPDF α β x = 0 := by
  simp [betaPDF_eq, hx.not_gt]

lemma betaPDF_of_pos_lt_one {α β x : ℝ} (hx_pos : 0 < x) (hx_lt : x < 1) :
    betaPDF α β x = ENNReal.ofReal ((1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
  rw [betaPDF_eq, if_pos ⟨hx_pos, hx_lt⟩]

lemma lintegral_betaPDF {α β : ℝ} :
    ∫⁻ x, betaPDF α β x =
      ∫⁻ (x : ℝ) in Ioo 0 1,
        ENNReal.ofReal
          (1 / beta α β * x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
  -- Show support is Ioo 0 1
  rw [← lintegral_add_compl _ measurableSet_Iic]
  rw [setLIntegral_congr_fun measurableSet_Iic
        (fun x (hx : x ≤ 0) ↦ betaPDF_eq_zero_of_nonpos hx),
      lintegral_zero]
  simp only [compl_Iic, zero_add]
  rw [← lintegral_add_compl _ measurableSet_Ici]
  rw [setLIntegral_congr_fun measurableSet_Ici
        (fun x (hx : 1 ≤ x) ↦ betaPDF_eq_zero_of_one_le hx),
      lintegral_zero]
  simp only [compl_Ici, measurableSet_Iio, Measure.restrict_restrict, zero_add]
  convert_to ∫⁻ x in Ioo 0 1, betaPDF α β x = _
  · convert rfl
    ext x
    simp only [mem_Ioo, mem_inter_iff, mem_Iio, mem_Ioi]
    tauto
  -- Apply betaPDF definition on Ioo 0 1
  rw [setLIntegral_congr_fun measurableSet_Ioo
        (fun x ⟨hx_pos, hx_lt⟩ ↦ betaPDF_of_pos_lt_one hx_pos hx_lt)]

/-- The beta pdf is positive for all positive reals with positive parameters. -/
lemma betaPDFReal_pos {α β x : ℝ} (hx : 0 < x ∧ x < 1) (hα : 0 < α) (hβ : 0 < β) :
     0 < betaPDFReal α β x := by
  unfold betaPDFReal
  have h_cond : 0 < x ∧ x < 1 := ⟨hx.1, hx.2⟩
  rw [if_pos h_cond]
  repeat apply mul_pos
  · simp only [zero_lt_one]
  · simp only [inv_pos]
    exact beta_pos hα hβ
  · have hx_pos : 0 < x := hx.1
    exact Real.rpow_pos_of_pos hx_pos (α - 1)
  have : 0 < (1 - x) := sub_pos.mpr hx.2
  exact Real.rpow_pos_of_pos this (β - 1)

/-- The beta pdf is measurable. -/
@[fun_prop, measurability]
lemma measurable_betaPDFReal (α β : ℝ) : Measurable (betaPDFReal α β) :=
  Measurable.ite measurableSet_Ioo (by fun_prop) (by fun_prop)

/-- The beta pdf is strongly measurable. -/
lemma stronglyMeasurable_betaPDFReal (α β : ℝ) :
    StronglyMeasurable (betaPDFReal α β) := by
  apply (measurable_betaPDFReal α β).stronglyMeasurable

/-- The pdf of the beta distribution integrates to 1. -/
@[simp]
lemma lintegral_betaPDF_eq_one {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫⁻ x, betaPDF α β x = 1 := by
  rw [lintegral_betaPDF, <-ENNReal.toReal_eq_one_iff,
    <-integral_eq_lintegral_of_nonneg_ae]
  · conv => lhs
            congr
            rfl
            ext
            rw [mul_assoc]
    rw [integral_const_mul]
    field_simp
    rw [div_eq_one_iff_eq (ne_of_gt (beta_pos hα hβ)),
      beta_eq_betaIntegralReal α β hα hβ]
    unfold betaIntegral
    rw [intervalIntegral.integral_of_le (by norm_num), <-integral_Ioc_eq_integral_Ioo]
    have (a : ℝ) (b : ℂ) : (a : ℂ) = b → a = b.re := by
      intro h
      simp only [← h, ofReal_re]
    apply this
    rw [← integral_complex_ofReal, setIntegral_congr_ae measurableSet_Ioc]
    simp only [mem_Ioc, ofReal_mul, and_imp]
    apply ae_of_all
    intro x hx0 hx1
    rw [ofReal_cpow (le_of_lt hx0) (α - 1)]
    have h_1_minus_x_nonneg : 0 ≤ 1 - x := by
      apply sub_nonneg.mpr
      exact hx1
    rw [ofReal_cpow h_1_minus_x_nonneg (β - 1)]; field_simp
  · apply Filter.Eventually.filter_mono
    · rw [Real.volume_eq_stieltjes_id]
    simp only [Pi.zero_apply, one_div, measurableSet_Ioo, ae_restrict_eq]
    refine Filter.eventually_inf_principal.mpr ?hf.hp.a
    simp only [mem_Ioo, and_imp]
    apply ae_of_all
    intro x h1 h2
    apply le_of_lt
    repeat apply mul_pos
    · exact inv_pos.mpr (beta_pos hα hβ)
    · exact Real.rpow_pos_of_pos h1 (α - 1)
    · exact Real.rpow_pos_of_pos (sub_pos.mpr h2) (β - 1)
  · apply (measurable_betaPDFReal α β).aestronglyMeasurable.congr
    unfold betaPDFReal
    rw [ae_eq_comm]
    simp only [measurableSet_Ioo, ae_restrict_eq, one_div]
    refine Filter.eventuallyEq_inf_principal_iff.mpr ?hfm.a
    simp only [mem_Ioo, left_eq_ite_iff, not_and, not_lt, mul_eq_zero,
      inv_eq_zero, and_imp]
    apply ae_of_all
    intro x h1 h2
    intro h'
    left
    have contra : ¬(0 < x → 1 ≤ x) := by
      intro h'
      have h3 : 1 ≤ x := h' h1
      exact lt_irrefl 1 (lt_of_le_of_lt h3 h2)
    exfalso
    exact contra h'

end BetaPDF

/-- Measure defined by the beta distribution. -/
noncomputable
def betaMeasure (α β : ℝ) : Measure ℝ :=
  volume.withDensity (betaPDF α β)

lemma isProbabilityMeasureBeta {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsProbabilityMeasure (betaMeasure α β) where
  measure_univ := by simp only [betaMeasure, MeasurableSet.univ,
    withDensity_apply, Measure.restrict_univ, lintegral_betaPDF_eq_one hα hβ]

end ProbabilityTheory
