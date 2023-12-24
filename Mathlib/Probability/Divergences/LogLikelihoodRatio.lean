/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Log-likelihood Ratio

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {f : α → ℝ}

section move_this

lemma todo_div [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    μ.rnDeriv ν =ᵐ[ν] fun x ↦ μ.rnDeriv (μ + ν) x / ν.rnDeriv (μ + ν) x := by
  have hν_ac : ν ≪ μ + ν := by
    rw [add_comm]; exact rfl.absolutelyContinuous.add_right _
  have h_pos := Measure.rnDeriv_pos hν_ac
  have h := Measure.rnDeriv_mul_rnDeriv hμν (κ := μ + ν)
  filter_upwards [hν_ac.ae_le h, h_pos, hν_ac.ae_le (Measure.rnDeriv_ne_top ν (μ + ν))]
    with x hx hx_pos hx_ne_top
  rw [Pi.mul_apply] at hx
  rwa [ENNReal.eq_div_iff hx_pos.ne' hx_ne_top, mul_comm]

end move_this

/-- Log-Likelihood Ratio between two measures. -/
noncomputable def LLR (μ ν : Measure α) (x : α) : ℝ := log (μ.rnDeriv ν x).toReal

lemma llr_def (μ ν : Measure α) : LLR μ ν = fun x ↦ log (μ.rnDeriv ν x).toReal := rfl

lemma exp_llr (μ ν : Measure α) [SigmaFinite μ] :
    (fun x ↦ exp (LLR μ ν x))
      =ᵐ[ν] fun x ↦ if μ.rnDeriv ν x = 0 then 1 else (μ.rnDeriv ν x).toReal := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [LLR, h_zero, ENNReal.zero_toReal, log_zero, exp_zero, ite_true]
  rw [LLR, exp_log, if_neg h_zero]
  rw [ENNReal.toReal_pos_iff]
  exact ⟨lt_of_le_of_ne (zero_le _) (Ne.symm h_zero), hx⟩

lemma exp_llr_of_ac (μ ν : Measure α) [SigmaFinite μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) :
    (fun x ↦ exp (LLR μ ν x)) =ᵐ[μ] fun x ↦ (μ.rnDeriv ν x).toReal := by
  filter_upwards [hμν.ae_le (exp_llr μ ν), Measure.rnDeriv_pos hμν] with x hx_eq hx_pos
  rw [hx_eq, if_neg hx_pos.ne']

lemma exp_llr_of_ac' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ) :
    (fun x ↦ exp (LLR μ ν x)) =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toReal := by
  filter_upwards [exp_llr μ ν, Measure.rnDeriv_pos' hμν] with x hx hx_pos
  rwa [if_neg hx_pos.ne'] at hx

lemma neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    - LLR μ ν =ᵐ[μ] LLR ν μ := by
  filter_upwards [Measure.inv_rnDeriv hμν] with x hx
  rw [Pi.neg_apply, LLR, LLR, ← log_inv, ← ENNReal.toReal_inv]
  congr

lemma exp_neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (fun x ↦ exp (- LLR μ ν x)) =ᵐ[μ] fun x ↦ (ν.rnDeriv μ x).toReal := by
  filter_upwards [neg_llr hμν, exp_llr_of_ac' ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply] at hx
  rw [hx, hx_exp_log]

@[measurability]
lemma measurable_llr (μ ν : Measure α) : Measurable (LLR μ ν) :=
  (Measure.measurable_rnDeriv μ ν).ennreal_toReal.log

@[measurability]
lemma stronglyMeasurable_llr (μ ν : Measure α) : StronglyMeasurable (LLR μ ν) :=
  (measurable_llr μ ν).stronglyMeasurable

lemma llr_smul_left [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    LLR (c • μ) ν =ᵐ[μ] fun x ↦ LLR μ ν x + log c.toReal := by
  simp only [LLR, llr_def]
  have h := Measure.rnDeriv_smul_left_of_ne_top μ ν hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [log_mul]
  rotate_left
  · rw [ENNReal.toReal_ne_zero]
    simp [hc, hc_ne_top]
  · rw [ENNReal.toReal_ne_zero]
    simp [hx_pos.ne', hx_ne_top.ne]
  ring

lemma llr_smul_right [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    LLR μ (c • ν) =ᵐ[μ] fun x ↦ LLR μ ν x - log c.toReal := by
  simp only [LLR, llr_def]
  have h := Measure.rnDeriv_smul_right_of_ne_top μ ν hc hc_ne_top
  filter_upwards [hμν.ae_le h, Measure.rnDeriv_pos hμν, hμν.ae_le (Measure.rnDeriv_lt_top μ ν)]
    with x hx_eq hx_pos hx_ne_top
  rw [hx_eq]
  simp only [Pi.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  rw [log_mul]
  rotate_left
  · rw [ENNReal.toReal_ne_zero]
    simp [hc, hc_ne_top]
  · rw [ENNReal.toReal_ne_zero]
    simp [hx_pos.ne', hx_ne_top.ne]
  rw [ENNReal.toReal_inv, log_inv]
  ring

section llr_tilted

variable [IsFiniteMeasure ν]

lemma llr_tilted_right [IsFiniteMeasure μ]
    (hμν : μ ≪ ν) (hf : Integrable (fun x ↦ exp (f x)) ν) :
    (LLR μ (ν.tilted f)) =ᵐ[μ] fun x ↦ - f x + log (∫ x, exp (f x) ∂ν) + LLR μ ν x := by
  cases eq_zero_or_neZero ν with
  | inl h =>
    have hμ : μ = 0 := by ext s _; exact hμν (by simp [h])
    simp only [hμ, ae_zero, Filter.EventuallyEq]; exact Filter.eventually_bot
  | inr h0 =>
    filter_upwards [hμν.ae_le (toReal_rnDeriv_tilted_right μ ν hf), Measure.rnDeriv_pos hμν,
      hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top
    rw [LLR, hx, log_mul, log_mul (exp_pos _).ne', log_exp, LLR]
    · exact (integral_exp_pos hf).ne'
    · refine (mul_pos (exp_pos _) (integral_exp_pos hf)).ne'
    · simp [ENNReal.toReal_eq_zero_iff, hx_lt_top.ne, hx_pos.ne']

lemma integrable_llr_tilted_right [IsFiniteMeasure μ] (hμν : μ ≪ ν) (hfμ : Integrable f μ)
    (h_int : Integrable (LLR μ ν) μ) (hfν : Integrable (fun x ↦ exp (f x)) ν) :
    Integrable (LLR μ (ν.tilted f)) μ := by
  rw [integrable_congr (llr_tilted_right hμν hfν)]
  exact Integrable.add (hfμ.neg.add (integrable_const _)) h_int

lemma integral_llr_tilted_right [IsProbabilityMeasure μ]
    (hμν : μ ≪ ν) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ exp (f x)) ν)
    (h_int : Integrable (LLR μ ν) μ) :
    ∫ x, LLR μ (ν.tilted f) x ∂μ = ∫ x, LLR μ ν x ∂μ - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) := by
  calc ∫ x, LLR μ (ν.tilted f) x ∂μ
    = ∫ x, - f x + log (∫ x, exp (f x) ∂ν) + LLR μ ν x ∂μ :=
        integral_congr_ae (llr_tilted_right hμν hfν)
  _ = - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) + ∫ x, LLR μ ν x ∂μ := by
        rw [← integral_neg, integral_add ?_ h_int]
        swap; · exact hfμ.neg.add (integrable_const _)
        rw [integral_add ?_ (integrable_const _)]
        swap; · exact hfμ.neg
        simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  _ = ∫ x, LLR μ ν x ∂μ - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) := by abel

end llr_tilted

lemma integrableOn_exp_neg_llr [SigmaFinite ν] [SigmaFinite μ] (hμν : μ ≪ ν)
    (s : Set α) (hνs : ν s ≠ ∞) :
    IntegrableOn (fun x ↦ exp (- LLR μ ν x)) s μ := by
  constructor
  · refine AEStronglyMeasurable.restrict ?_
    refine StronglyMeasurable.aestronglyMeasurable ?_
    exact (measurable_llr _ _).neg.exp.stronglyMeasurable
  · rw [hasFiniteIntegral_def]
    set t := toMeasurable ν s with ht_eq
    have ht : MeasurableSet t := measurableSet_toMeasurable ν s
    have hνt : ν t ≠ ∞ := by rwa [ht_eq, measure_toMeasurable s]
    calc ∫⁻ a in s, ‖rexp (-LLR μ ν a)‖₊ ∂μ
      ≤ ∫⁻ a in t, ‖rexp (-LLR μ ν a)‖₊ ∂μ := lintegral_mono_set (subset_toMeasurable ν s)
    _ = ∫⁻ a in t, ‖(ν.rnDeriv μ a).toReal‖₊ ∂μ := by
        refine set_lintegral_congr_fun ht ?_
        filter_upwards [exp_neg_llr hμν] with x hx _
        rw [hx]
    _ = ∫⁻ a in t, ν.rnDeriv μ a ∂μ := by
        refine set_lintegral_congr_fun ht ?_
        filter_upwards [Measure.rnDeriv_ne_top ν μ] with x hx _
        rw [← ofReal_norm_eq_coe_nnnorm]
        simp [hx]
    _ ≤ ν t := Measure.set_lintegral_rnDeriv_le t
    _ < ∞ := hνt.lt_top


end MeasureTheory
