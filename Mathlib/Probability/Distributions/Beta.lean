/-
Copyright (c) 2025 Tommy Löfgren . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tommy Löfgren
-/
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Probability.CDF

/-! # Beta distributions over ℝ

Define the beta measure over the reals.

## Main definitions
* `betaPDFReal`: the function `α β x ↦ (1 / Beta α β) * x^(α - 1) * (1 - x)^(β - 1)`
  for `0 < x ∧ x < 1` or `0` else, which is the probability density function of a beta distribution
  with shape parameters `α` and `β` (when `hα : 0 < α ` and `hβ : 0 < β`).
* `betaPDF`: `ℝ≥0∞`-valued pdf,
  `betaPDF α β = ENNReal.ofReal (betaPDFReal α β)`.
* `betaMeasure`: a beta measure on `ℝ`, parametrized by its shape `α` and `β`.
* `betaCDFReal`: the CDF given by the definition of CDF in `ProbabilityTheory.CDF` applied to the
  beta measure.
-/

open scoped ENNReal NNReal

open MeasureTheory Complex Set

namespace ProbabilityTheory

section BetaPDF

/-- The Beta function over the reals -/
noncomputable def betaIntegralReal (α β : ℝ) : ℝ :=
  (betaIntegral α β).re

/-- Beta is the normalizing constant in the beta distribution -/
noncomputable def Beta (α β : ℝ) : ℝ :=
  Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)

lemma betaIntegral_eq (u v : ℂ) (hu : u.re > 0) (hv : v.re > 0):
  betaIntegral u v = Gamma u * Gamma v / Gamma (u + v) := by
    rw [Gamma_mul_Gamma_eq_betaIntegral hu hv, mul_comm]
    have hne : Gamma (u + v) ≠ 0 := by
      apply Gamma_ne_zero; intro m
      have h_sum_re : (u + v).re > 0 := by
        simp only [add_re]; exact add_pos hu hv
      simp; rw [Complex.ext_iff]
      rintro ⟨hre, him⟩
      rw [hre] at h_sum_re
      simp at h_sum_re
      have : (↑m : ℝ) ≥ 0 := by exact Nat.cast_nonneg m
      apply absurd h_sum_re (not_lt_of_ge this)
    field_simp [hne]

lemma Beta_eq (α β : ℝ) :
  Beta α β = (Gamma α * Gamma β / Gamma (α + β)).re := by
  unfold Beta; rw [← Complex.ofReal_add α β]
  repeat rw [_root_.Complex.Gamma_ofReal]
  simp

lemma Beta_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β): Beta α β > 0 := by
  unfold Beta
  have h1 : 0 < Real.Gamma α := Real.Gamma_pos_of_pos hα
  have h2 : 0 < Real.Gamma β := Real.Gamma_pos_of_pos hβ
  have h3 : 0 < Real.Gamma (α + β) := Real.Gamma_pos_of_pos (add_pos hα hβ)
  apply div_pos (mul_pos h1 h2); exact h3

lemma Beta_inv_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : 0 < (Beta α β)⁻¹ := by
  exact inv_pos.mpr (Beta_pos hα hβ)

/-- Relation between the Beta function and the gamma function over the reals. -/
theorem Beta_eq_betaIntegralReal (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
  Beta α β = betaIntegralReal α β := by
  unfold betaIntegralReal; rw [Beta_eq]
  let α' : ℂ := ↑α
  let β' : ℂ := ↑β
  have hα' : α'.re > 0 := by
    simp [α']; exact hα
  have hβ' : β'.re > 0 := by
    simp [β']; exact hβ
  rw [betaIntegral_eq α' β' hα' hβ']

lemma betaIntegralReal_eq (α β : ℝ) (hα : 0 < α) (hβ : 0 < β):
 betaIntegralReal α β = betaIntegral α β := by
  rw [<-Beta_eq_betaIntegralReal α β hα hβ, Complex.ext_iff]
  constructor
  · rw [betaIntegral_eq α β hα hβ, <-Beta_eq]; simp
  have : (Gamma α * Gamma β / Gamma (α + β)).im = 0 := by
    rw [← Complex.ofReal_add α β]
    repeat rw [_root_.Complex.Gamma_ofReal]
    unfold Real.Gamma; simp
  rw [betaIntegral_eq α β hα hβ, this]; simp

noncomputable def betaPDFReal (α β x : ℝ) : ℝ :=
  if 0 < x ∧ x < 1 then
    (1 / Beta α β) * x^(α - 1) * (1 - x)^(β - 1)
  else
    0

/-- The pdf of the beta distribution, as a function valued in `ℝ≥0∞` -/
noncomputable def betaPDF (α β x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (betaPDFReal α β x)

lemma betaPDF_eq (α β x : ℝ) :
    betaPDF α β x =
      ENNReal.ofReal (if 0 < x ∧ x < 1 then
      (1 / Beta α β) * x^(α - 1) * (1 - x)^(β - 1) else 0) := by
      rfl

lemma betaPDF_eq_zero_of_le_zero {α β x : ℝ} (hx : x ≤ 0) :
  betaPDF α β x = 0 := by
  rw [betaPDF_eq]
  have : ¬ (0 < x ∧ x < 1) := by
    intro h
    exact lt_irrefl 0 (lt_of_lt_of_le h.1 hx)
  rw [if_neg this, ENNReal.ofReal_zero]

lemma betaPDF_eq_zero_of_one_le {α β x : ℝ} (hx : 1 ≤ x) :
  betaPDF α β x = 0 := by
  rw [betaPDF_eq]
  have : ¬ (0 < x ∧ x < 1) := by
    intro h
    exact lt_irrefl 1 (lt_of_le_of_lt hx h.2)
  rw [if_neg this, ENNReal.ofReal_zero]

lemma betaPDF_eq_of_ge_zero_le_one {α β x : ℝ}
    (hx : 0 < x ∧ x < 1) :
  betaPDF α β x = ENNReal.ofReal (
    (1 / Beta α β) * x^(α - 1) * (1 - x)^(β - 1)) := by
  rw [betaPDF_eq]
  have h : 0 < x ∧ x < 1 :=
    ⟨hx.1, hx.2⟩
  rw [if_pos h]

lemma lintegral_betaPDF_eq {α β : ℝ} : ∫⁻ x, betaPDF α β x
  = ∫⁻ (x : ℝ) in Set.Ioo 0 1, ENNReal.ofReal (1 / Beta α β * x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
  have left_zero : ∫⁻ x in Iic 0, betaPDF α β x = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Iic
    (ae_of_all _ (fun x (hx : x ≤ 0) ↦ betaPDF_eq_zero_of_le_zero hx)),
      lintegral_zero]
  have right_zero : ∫⁻ x in Ici 1, betaPDF α β x ∂volume.restrict (Ioi 0) = 0 := by
    rw [setLIntegral_congr_fun measurableSet_Ici
    (ae_of_all _ (fun x (hx : 1 ≤ x) ↦ betaPDF_eq_zero_of_one_le hx)),
      lintegral_zero]
  have middle : ∫⁻ x in Ioo 0 1, betaPDF α β x =
    ∫⁻ x in Ioo 0 1, ENNReal.ofReal ((1 / Beta α β) * x^(α - 1) * (1 - x)^(β - 1)) := by
    rw [setLIntegral_congr_fun measurableSet_Ioo
    (ae_of_all _ (fun x (hx : 0 < x ∧ x < 1) ↦ betaPDF_eq_of_ge_zero_le_one hx))]
  have : ∫⁻ x, betaPDF α β x = ∫⁻ x in Ioo 0 1, betaPDF α β x := by
    rw [← lintegral_add_compl _ measurableSet_Iic, left_zero]; simp
    rw [← lintegral_add_compl _ measurableSet_Ici, right_zero]; simp
    convert rfl; ext x; simp; tauto
  rw [this, middle]

/-- The beta pdf is positive for all positive reals with positive parameters -/
lemma betaPDFReal_pos {α β x : ℝ} (hx : 0 < x ∧ x < 1) (hα: α > 0) (hβ: β > 0):
  betaPDFReal α β x > 0 := by
  unfold betaPDFReal
  have h_cond : 0 < x ∧ x < 1 := ⟨hx.1, hx.2⟩
  rw [if_pos h_cond]
  repeat apply mul_pos
  · simp
  · simp; exact Beta_pos hα hβ
  · have hx_pos : 0 < x := hx.1
    exact Real.rpow_pos_of_pos hx_pos (α - 1)
  have : (1 - x) > 0 := sub_pos.mpr hx.2
  exact Real.rpow_pos_of_pos this (β - 1)

lemma betaPDFReal_pos_Ioo {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
  ∀ z ∈ Set.Ioo 0 1, 0 < betaPDFReal α β z := by
    intros z hz
    exact betaPDFReal_pos ⟨hz.1, hz.2⟩ hα hβ

/-- The beta pdf is measurable. -/
@[fun_prop, measurability]
lemma measurable_betaPDFReal (α β : ℝ) : Measurable (betaPDFReal α β) := by
  apply Measurable.ite measurableSet_Ioo
  · repeat apply Measurable.mul
    repeat apply measurable_const
    · apply measurable_id'.pow_const (α - 1)
    apply Measurable.pow_const
    exact Measurable.const_sub measurable_id (1 : ℝ)
  exact measurable_const

/-- The beta pdf is strongly measurable -/
lemma stronglyMeasurable_betaPDFReal (α β : ℝ) :
    StronglyMeasurable (betaPDFReal α β) := by
    apply (measurable_betaPDFReal α β).stronglyMeasurable

/-- The pdf of the beta distribution integrates to 1 -/
@[simp]
lemma lintegral_betaPDF_eq_one {α β: ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫⁻ x, betaPDF α β x = 1 := by
  rw [lintegral_betaPDF_eq, <-ENNReal.toReal_eq_one_iff, <-integral_eq_lintegral_of_nonneg_ae];
  · -- Move Beta outside of the integral and simplify
    conv => lhs; congr; rfl; ext; rw [mul_assoc]
    rw [integral_const_mul]
    field_simp; rw [div_eq_one_iff_eq (ne_of_gt (Beta_pos hα hβ))]
    -- Use relationship Beta and Gamma
    rw [Beta_eq_betaIntegralReal α β hα hβ]; unfold betaIntegralReal betaIntegral
    rw [intervalIntegral.integral_of_le (by norm_num), <-integral_Ioc_eq_integral_Ioo]
    have (a : ℝ) (b : ℂ) : (a : ℂ) = b → a = b.re := by intro h; simp [← h]
    apply this; rw [← integral_complex_ofReal]
    rw [setIntegral_congr_ae measurableSet_Ioc]
    simp; apply ae_of_all; intro x hx0 hx1
    rw [ofReal_cpow (le_of_lt hx0) (α - 1)]
    have h_1_minus_x_nonneg : 0 ≤ 1 - x := by
      apply sub_nonneg.mpr
      exact hx1
    rw [ofReal_cpow h_1_minus_x_nonneg (β - 1)]; field_simp
  · apply Filter.Eventually.filter_mono;
    · rw [Real.volume_eq_stieltjes_id]
    simp; refine Filter.eventually_inf_principal.mpr ?hf.hp.a
    simp; apply ae_of_all; intro x h1 h2; apply le_of_lt;repeat apply mul_pos
    · exact Beta_inv_pos hα hβ
    · exact Real.rpow_pos_of_pos h1 (α - 1)
    · exact Real.rpow_pos_of_pos (sub_pos.mpr h2) (β - 1)
  · apply (measurable_betaPDFReal α β).aestronglyMeasurable.congr
    unfold betaPDFReal; rw [ae_eq_comm]; simp
    refine Filter.eventuallyEq_inf_principal_iff.mpr ?hfm.a
    simp; apply ae_of_all; intro x h1 h2
    have h : 0 < x ∧ x < 1 := ⟨h1, h2⟩
    intro h'; left; have contra : ¬(0 < x → 1 ≤ x) := by
      intro h'
      have h3 : 1 ≤ x := h' h1
      exact lt_irrefl 1 (lt_of_le_of_lt h3 h2)
    exfalso
    exact contra h'

end BetaPDF

/-- Measure defined by the beta distribution -/
noncomputable
def betaMeasure (α β : ℝ) : Measure ℝ :=
  volume.withDensity (betaPDF α β)

lemma isProbabilityMeasureBeta {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsProbabilityMeasure (betaMeasure α β) where
  measure_univ := by simp [betaMeasure, lintegral_betaPDF_eq_one hα hβ]

section BetaCDF

/-- CDF of the beta distribution -/
noncomputable
def betaCDFReal (α β : ℝ) : StieltjesFunction :=
  cdf (betaMeasure α β)

end BetaCDF

end ProbabilityTheory
