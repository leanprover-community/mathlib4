/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Log-likelihood Ratio

The likelihood ratio between two measures `μ` and `ν` is their Radon-Nikodym derivative
`μ.rnDeriv ν`. The logarithm of that function is often used instead: this is the log-likelihood
ratio.

This file contains a definition of the log-likelihood ratio (llr) and its properties.

## Main definitions

* `llr μ ν`: Log-Likelihood Ratio between `μ` and `ν`, defined as the function
  `x ↦ log (μ.rnDeriv ν x).toReal`.

-/

open Real

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {f : α → ℝ}

/-- Log-Likelihood Ratio between two measures. -/
noncomputable def llr (μ ν : Measure α) (x : α) : ℝ := log (μ.rnDeriv ν x).toReal

lemma llr_def (μ ν : Measure α) : llr μ ν = fun x ↦ log (μ.rnDeriv ν x).toReal := rfl

lemma llr_self (μ : Measure α) [SigmaFinite μ] : llr μ μ =ᵐ[μ] 0 := by
  filter_upwards [μ.rnDeriv_self] with a ha using by simp [llr, ha]

lemma exp_llr (μ ν : Measure α) [SigmaFinite μ] :
    (fun x ↦ exp (llr μ ν x))
      =ᵐ[ν] fun x ↦ if μ.rnDeriv ν x = 0 then 1 else (μ.rnDeriv ν x).toReal := by
  filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
  by_cases h_zero : μ.rnDeriv ν x = 0
  · simp only [llr, h_zero, ENNReal.toReal_zero, log_zero, exp_zero, ite_true]
  · rw [llr, exp_log, if_neg h_zero]
    exact ENNReal.toReal_pos h_zero hx.ne

lemma exp_llr_of_ac (μ ν : Measure α) [SigmaFinite μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) :
    (fun x ↦ exp (llr μ ν x)) =ᵐ[μ] fun x ↦ (μ.rnDeriv ν x).toReal := by
  filter_upwards [hμν.ae_le (exp_llr μ ν), Measure.rnDeriv_pos hμν] with x hx_eq hx_pos
  rw [hx_eq, if_neg hx_pos.ne']

lemma exp_llr_of_ac' (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ) :
    (fun x ↦ exp (llr μ ν x)) =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toReal := by
  filter_upwards [exp_llr μ ν, Measure.rnDeriv_pos' hμν] with x hx hx_pos
  rwa [if_neg hx_pos.ne'] at hx

lemma neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    -llr μ ν =ᵐ[μ] llr ν μ := by
  filter_upwards [Measure.inv_rnDeriv hμν] with x hx
  rw [Pi.neg_apply, llr, llr, ← log_inv, ← ENNReal.toReal_inv]
  congr

lemma exp_neg_llr [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    (fun x ↦ exp (-llr μ ν x)) =ᵐ[μ] fun x ↦ (ν.rnDeriv μ x).toReal := by
  filter_upwards [neg_llr hμν, exp_llr_of_ac' ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply] at hx
  rw [hx, hx_exp_log]

lemma exp_neg_llr' [SigmaFinite μ] [SigmaFinite ν] (hμν : ν ≪ μ) :
    (fun x ↦ exp (-llr μ ν x)) =ᵐ[ν] fun x ↦ (ν.rnDeriv μ x).toReal := by
  filter_upwards [neg_llr hμν, exp_llr_of_ac ν μ hμν] with x hx hx_exp_log
  rw [Pi.neg_apply, neg_eq_iff_eq_neg] at hx
  rw [← hx, hx_exp_log]

@[measurability, fun_prop]
lemma measurable_llr (μ ν : Measure α) : Measurable (llr μ ν) :=
  (Measure.measurable_rnDeriv μ ν).ennreal_toReal.log

@[measurability]
lemma stronglyMeasurable_llr (μ ν : Measure α) : StronglyMeasurable (llr μ ν) :=
  (measurable_llr μ ν).stronglyMeasurable

lemma llr_smul_left [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    (hμν : μ ≪ ν) (c : ℝ≥0∞) (hc : c ≠ 0) (hc_ne_top : c ≠ ∞) :
    llr (c • μ) ν =ᵐ[μ] fun x ↦ llr μ ν x + log c.toReal := by
  simp only [llr, llr_def]
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
    llr μ (c • ν) =ᵐ[μ] fun x ↦ llr μ ν x - log c.toReal := by
  simp only [llr, llr_def]
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

lemma integrable_rnDeriv_mul_log_iff [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) :
    Integrable (fun a ↦ (μ.rnDeriv ν a).toReal * log (μ.rnDeriv ν a).toReal) ν
      ↔ Integrable (llr μ ν) μ :=
  integrable_rnDeriv_smul_iff hμν

lemma integral_rnDeriv_mul_log [SigmaFinite μ] [μ.HaveLebesgueDecomposition ν] (hμν : μ ≪ ν) :
    ∫ a, (μ.rnDeriv ν a).toReal * log (μ.rnDeriv ν a).toReal ∂ν = ∫ a, llr μ ν a ∂μ := by
  simp_rw [← smul_eq_mul, integral_rnDeriv_smul hμν, llr]

section llr_tilted

lemma llr_tilted_left [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    (hf : Integrable (fun x ↦ exp (f x)) μ) (hfν : AEMeasurable f ν) :
    (llr (μ.tilted f) ν) =ᵐ[μ] fun x ↦ f x - log (∫ z, exp (f z) ∂μ) + llr μ ν x := by
  cases eq_zero_or_neZero μ with
  | inl hμ =>
    simp only [hμ, ae_zero, Filter.EventuallyEq, Filter.eventually_bot]
  | inr h0 =>
    filter_upwards [hμν.ae_le (toReal_rnDeriv_tilted_left μ hfν), Measure.rnDeriv_pos hμν,
      hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top
    rw [llr, hx, log_mul, div_eq_mul_inv, log_mul (exp_pos _).ne', log_exp, log_inv, llr,
      ← sub_eq_add_neg]
    · simp only [ne_eq, inv_eq_zero]
      exact (integral_exp_pos hf).ne'
    · simp only [ne_eq, div_eq_zero_iff]
      push_neg
      exact ⟨(exp_pos _).ne', (integral_exp_pos hf).ne'⟩
    · simp [ENNReal.toReal_eq_zero_iff, hx_lt_top.ne, hx_pos.ne']

lemma integrable_llr_tilted_left [IsFiniteMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hf : Integrable f μ) (h_int : Integrable (llr μ ν) μ)
    (hfμ : Integrable (fun x ↦ exp (f x)) μ) (hfν : AEMeasurable f ν) :
    Integrable (llr (μ.tilted f) ν) μ := by
  rw [integrable_congr (llr_tilted_left hμν hfμ hfν)]
  exact Integrable.add (hf.sub (integrable_const _)) h_int

lemma integral_llr_tilted_left [IsProbabilityMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hf : Integrable f μ) (h_int : Integrable (llr μ ν) μ)
    (hfμ : Integrable (fun x ↦ exp (f x)) μ) (hfν : AEMeasurable f ν) :
    ∫ x, llr (μ.tilted f) ν x ∂μ = ∫ x, llr μ ν x ∂μ + ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ) := by
  calc ∫ x, llr (μ.tilted f) ν x ∂μ
    = ∫ x, f x - log (∫ x, exp (f x) ∂μ) + llr μ ν x ∂μ :=
        integral_congr_ae (llr_tilted_left hμν hfμ hfν)
  _ = ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ) + ∫ x, llr μ ν x ∂μ := by
        rw [integral_add ?_ h_int]
        swap; · exact hf.sub (integrable_const _)
        rw [integral_sub hf (integrable_const _)]
        simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  _ = ∫ x, llr μ ν x ∂μ + ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂μ) := by abel

lemma llr_tilted_right [SigmaFinite μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hf : Integrable (fun x ↦ exp (f x)) ν) :
    (llr μ (ν.tilted f)) =ᵐ[μ] fun x ↦ -f x + log (∫ z, exp (f z) ∂ν) + llr μ ν x := by
  cases eq_zero_or_neZero ν with
  | inl h =>
    have hμ : μ = 0 := by ext s _; exact hμν (by simp [h])
    simp only [hμ, ae_zero, Filter.EventuallyEq, Filter.eventually_bot]
  | inr h0 =>
    filter_upwards [hμν.ae_le (toReal_rnDeriv_tilted_right μ ν hf), Measure.rnDeriv_pos hμν,
      hμν.ae_le (Measure.rnDeriv_lt_top μ ν)] with x hx hx_pos hx_lt_top
    rw [llr, hx, log_mul, log_mul (exp_pos _).ne', log_exp, llr]
    · exact (integral_exp_pos hf).ne'
    · refine (mul_pos (exp_pos _) (integral_exp_pos hf)).ne'
    · simp [ENNReal.toReal_eq_zero_iff, hx_lt_top.ne, hx_pos.ne']

lemma integrable_llr_tilted_right [IsFiniteMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hfμ : Integrable f μ)
    (h_int : Integrable (llr μ ν) μ) (hfν : Integrable (fun x ↦ exp (f x)) ν) :
    Integrable (llr μ (ν.tilted f)) μ := by
  rw [integrable_congr (llr_tilted_right hμν hfν)]
  exact Integrable.add (hfμ.neg.add (integrable_const _)) h_int

lemma integral_llr_tilted_right [IsProbabilityMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (hfμ : Integrable f μ) (hfν : Integrable (fun x ↦ exp (f x)) ν)
    (h_int : Integrable (llr μ ν) μ) :
    ∫ x, llr μ (ν.tilted f) x ∂μ = ∫ x, llr μ ν x ∂μ - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) := by
  calc ∫ x, llr μ (ν.tilted f) x ∂μ
    = ∫ x, -f x + log (∫ x, exp (f x) ∂ν) + llr μ ν x ∂μ :=
        integral_congr_ae (llr_tilted_right hμν hfν)
  _ = -∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) + ∫ x, llr μ ν x ∂μ := by
        rw [← integral_neg, integral_add ?_ h_int]
        swap; · exact hfμ.neg.add (integrable_const _)
        rw [integral_add ?_ (integrable_const _)]
        swap; · exact hfμ.neg
        simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  _ = ∫ x, llr μ ν x ∂μ - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) := by abel

end llr_tilted

end MeasureTheory
