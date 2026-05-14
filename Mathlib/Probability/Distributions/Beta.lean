/-
Copyright (c) 2025 Tommy Löfgren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tommy Löfgren
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-! # Beta distributions over ℝ

Define the beta distribution over the reals.

## Main definitions
* `betaPDFReal`: the function `α β x ↦ (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1)`
  for `0 < x ∧ x < 1` or `0` else, which is the probability density function of a beta distribution
  with shape parameters `α` and `β` (when `0 < α` and `0 < β`).
* `betaPDF`: `ℝ≥0∞`-valued pdf,
  `betaPDF α β = ENNReal.ofReal (betaPDFReal α β)`.
-/

@[expose] public section

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
      ∫⁻ (x : ℝ) in Ioo 0 1, ENNReal.ofReal (1 / beta α β * x ^ (α - 1) * (1 - x) ^ (β - 1)) := by
  rw [← lintegral_add_compl _ measurableSet_Iic,
    setLIntegral_eq_zero measurableSet_Iic (fun x (hx : x ≤ 0) ↦ betaPDF_eq_zero_of_nonpos hx),
    zero_add, compl_Iic, ← lintegral_add_compl _ measurableSet_Ici,
    setLIntegral_eq_zero measurableSet_Ici (fun x (hx : 1 ≤ x) ↦ betaPDF_eq_zero_of_one_le hx),
    zero_add, compl_Ici, Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi,
    setLIntegral_congr_fun measurableSet_Ioo
      (fun x ⟨hx_pos, hx_lt⟩ ↦ betaPDF_of_pos_lt_one hx_pos hx_lt)]

/-- The beta pdf is positive for all positive reals with positive parameters. -/
lemma betaPDFReal_pos {α β x : ℝ} (hx1 : 0 < x) (hx2 : x < 1) (hα : 0 < α) (hβ : 0 < β) :
    0 < betaPDFReal α β x := by
  rw [betaPDFReal, if_pos ⟨hx1, hx2⟩]
  exact mul_pos (mul_pos (one_div_pos.2 (beta_pos hα hβ)) (Real.rpow_pos_of_pos hx1 (α - 1)))
    (Real.rpow_pos_of_pos (by linarith) (β - 1))

/-- The beta pdf is measurable. -/
@[fun_prop]
lemma measurable_betaPDFReal (α β : ℝ) : Measurable (betaPDFReal α β) :=
  Measurable.ite measurableSet_Ioo (by fun_prop) (by fun_prop)

/-- The beta pdf is strongly measurable. -/
@[fun_prop]
lemma stronglyMeasurable_betaPDFReal (α β : ℝ) :
    StronglyMeasurable (betaPDFReal α β) := (measurable_betaPDFReal α β).stronglyMeasurable

/-- The pdf of the beta distribution integrates to 1. -/
@[simp]
lemma lintegral_betaPDF_eq_one {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫⁻ x, betaPDF α β x = 1 := by
  rw [lintegral_betaPDF, ← ENNReal.toReal_eq_one_iff, ← integral_eq_lintegral_of_nonneg_ae]
  · simp_rw [mul_assoc, integral_const_mul]
    field_simp
    rw [div_eq_one_iff_eq (ne_of_gt (beta_pos hα hβ)), beta_eq_betaIntegralReal α β hα hβ,
      betaIntegral, intervalIntegral.integral_of_le (by norm_num),
      ← integral_Ioc_eq_integral_Ioo, ← RCLike.re_to_complex, ← integral_re]
    · refine setIntegral_congr_fun measurableSet_Ioc fun x ⟨hx1, hx₂⟩ ↦ ?_
      norm_cast
      rw [← Complex.ofReal_cpow, ← Complex.ofReal_cpow, RCLike.re_to_complex,
        Complex.re_mul_ofReal, Complex.ofReal_re]
      all_goals linarith
    convert betaIntegral_convergent (u := α) (v := β) (by simpa) (by simpa)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by simp), IntegrableOn]
  · refine ae_restrict_of_forall_mem measurableSet_Ioo (fun x hx ↦ ?_)
    convert betaPDFReal_pos hx.1 hx.2 hα hβ |>.le using 1
    rw [betaPDFReal, if_pos ⟨hx.1, hx.2⟩]
  · exact Measurable.aestronglyMeasurable (by fun_prop)

end BetaPDF

/-- Measure defined by the beta distribution. -/
noncomputable
def betaMeasure (α β : ℝ) : Measure ℝ :=
  volume.withDensity (betaPDF α β)

lemma isProbabilityMeasureBeta {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsProbabilityMeasure (betaMeasure α β) where
  measure_univ := by simp [betaMeasure, lintegral_betaPDF_eq_one hα hβ]

end ProbabilityTheory
