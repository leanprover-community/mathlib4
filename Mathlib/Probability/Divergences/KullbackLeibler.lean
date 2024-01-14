/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.Probability.Divergences.FDivergence
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Kullback-Leibler divergence

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

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

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

/-- Kullback-Leibler divergence between two measures, real-valued version. -/
noncomputable def klReal (μ ν : Measure α) : ℝ := ∫ x, llr μ ν x ∂μ

open Classical in
/-- Kullback-Leibler divergence between two measures. -/
noncomputable
def kl (μ ν : Measure α) : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ then ENNReal.ofReal (∫ x, llr μ ν x ∂μ) else ∞

@[simp]
lemma klReal_of_not_integrable (h : ¬ Integrable (llr μ ν) μ) : klReal μ ν = 0 := by
  rw [klReal, integral_undef h]

section llr_and_lrf

lemma integrable_lrf_mul_log [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    Integrable (LRf (fun x ↦ x * log x) μ ν) ν :=
  integrable_rnDeriv_smul hμν h_int

lemma klReal_eq_fDiv_mul_log [SigmaFinite μ] [Measure.HaveLebesgueDecomposition μ ν] (hμν : μ ≪ ν) :
    klReal μ ν = fDiv (fun x ↦ x * log x) μ ν := by
  simp_rw [klReal, llr, fDiv, LRf]
  conv_lhs =>
    rw [← Measure.withDensity_rnDeriv_eq _ _ hμν]
    conv in (Measure.rnDeriv (ν.withDensity (μ.rnDeriv ν)) ν) =>
      rw [Measure.withDensity_rnDeriv_eq _ _ hμν]
  have h_rn_eq : μ.rnDeriv ν =ᵐ[ν] fun x ↦ (μ.rnDeriv ν x).toNNReal := by
    filter_upwards [Measure.rnDeriv_lt_top μ ν] with x hx
    rw [ENNReal.coe_toNNReal]
    exact hx.ne
  have h_ν_eq : ν.withDensity (μ.rnDeriv ν)
      = ν.withDensity (fun x ↦ (μ.rnDeriv ν x).toNNReal) := withDensity_congr_ae h_rn_eq
  conv_lhs => rw [h_ν_eq]
  rw [integral_withDensity_eq_integral_smul]
  swap; · exact (Measure.measurable_rnDeriv _ _).ennreal_toNNReal
  congr

end llr_and_lrf

section klReal_nonneg

lemma klReal_ge_mul_log' [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    (μ Set.univ).toReal * log (μ Set.univ).toReal ≤ klReal μ ν :=
  (le_fDiv Real.convexOn_mul_log Real.continuous_mul_log.continuousOn
    (integrable_lrf_mul_log hμν h_int) hμν).trans_eq (klReal_eq_fDiv_mul_log hμν).symm

lemma klReal_ge_mul_log [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    (μ Set.univ).toReal * log ((μ Set.univ).toReal / (ν Set.univ).toReal) ≤ klReal μ ν := by
  by_cases hμ : μ = 0
  · simp [klReal, hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    apply? says exact Measure.measure_univ_eq_zero.mp (hμν rfl)
  let ν' := (ν Set.univ)⁻¹ • ν
  have : IsProbabilityMeasure ν' := by
    constructor
    simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm, ENNReal.mul_inv_cancel]
    · simp [hν]
    · exact measure_ne_top _ _
  have h := klReal_ge_mul_log' (?_ : μ ≪ ν') ?_
  rotate_left
  · refine Measure.AbsolutelyContinuous.trans hμν ?_
    refine Measure.absolutelyContinuous_of_le_smul (c := ν Set.univ) ?_
    rw [← smul_assoc, smul_eq_mul, ENNReal.mul_inv_cancel, one_smul]
    · simp [hν]
    · exact measure_ne_top _ _
  · rw [integrable_congr (llr_smul_right hμν (ν Set.univ)⁻¹ _ _)]
    rotate_left
    · simp [measure_ne_top ν _]
    · simp [hν]
    exact h_int.sub (integrable_const _)
  rw [klReal, integral_congr_ae (llr_smul_right hμν (ν Set.univ)⁻¹ _ _)] at h
  rotate_left
  · simp [measure_ne_top ν _]
  · simp [hν]
  rw [integral_sub h_int (integrable_const _), integral_const, smul_eq_mul, le_sub_iff_add_le,
    ENNReal.toReal_inv, log_inv, mul_neg, ← sub_eq_add_neg] at h
  rwa [log_div, mul_sub]
  · rw [ENNReal.toReal_ne_zero]
    simp [hμ, measure_ne_top μ]
  · rw [ENNReal.toReal_ne_zero]
    simp [hν, measure_ne_top ν]

lemma klReal_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hμν : μ ≪ ν) :
    0 ≤ klReal μ ν := by
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [klReal_eq_fDiv_mul_log hμν]
    exact fDiv_nonneg Real.convexOn_mul_log Real.continuous_mul_log.continuousOn
      (by simp) (integrable_lrf_mul_log hμν h_int) hμν
  · rw [klReal, integral_undef h_int]

end klReal_nonneg

lemma klReal_tilted_right [IsProbabilityMeasure μ] [SigmaFinite ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
    {f : α → ℝ} (hfμ : Integrable f μ) (hf : Integrable (fun x ↦ exp (f x)) ν) :
    klReal μ (ν.tilted f) = klReal μ ν - ∫ x, f x ∂μ + log (∫ x, exp (f x) ∂ν) :=
  integral_llr_tilted_right hμν hfμ hf h_int

lemma integral_sub_log_integral_exp_le_klReal [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ)
    (f : α → ℝ) (hfμ : Integrable f μ) (hf : Integrable (fun x ↦ exp (f x)) ν) :
    ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) ≤ klReal μ ν := by
  have : klReal μ ν - klReal μ (ν.tilted f) = ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) := by
    rw [klReal_tilted_right hμν h_int hfμ hf]
    abel
  rw [← this]
  simp only [tsub_le_iff_right, le_add_iff_nonneg_right]
  have : IsProbabilityMeasure (Measure.tilted ν f) := isProbabilityMeasure_tilted hf
  exact klReal_nonneg (hμν.trans (absolutelyContinuous_tilted hf))

/-- One side of the Donsker-Varadhan variational formula for the Kullback-Leibler divergence.
See `klReal_eq_ciSup` for the equality. -/
lemma ciSup_le_klReal [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν)
      ≤ klReal μ ν := by
  refine ciSup_le (fun f ↦ ?_)
  by_cases hfμ : Integrable f μ
  · simp only [hfμ, ciSup_unique]
    by_cases hf : Integrable (fun x ↦ exp (f x)) ν
    · simp only [hf, ciSup_unique]
      exact integral_sub_log_integral_exp_le_klReal hμν h_int f hfμ hf
    · simp [hf, ciSup_empty]
      exact klReal_nonneg hμν
  · simp only [hfμ, ciSup_empty]
    exact klReal_nonneg hμν

lemma klReal_le_integral_llrAddConst [IsFiniteMeasure μ] [Measure.HaveLebesgueDecomposition μ ν]
    {u : ℝ} (hu : 0 ≤ u) (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    klReal μ ν ≤ ∫ x, llrAddConst μ ν u x ∂μ :=
  integral_mono_ae h_int (integrable_llrAddConst hu h_int) (llr_le_llrAddConst hu hμν)

lemma klReal_le_ciInf_integral_llrAddConst [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    klReal μ ν ≤ ⨅ u : {v // (0 : ℝ) < v}, ∫ x, llrAddConst μ ν u x ∂μ :=
  le_ciInf (fun u ↦ klReal_le_integral_llrAddConst u.2.le hμν h_int)

lemma integral_llrAddConst_le_ciSup_add [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) {u : ℝ} (hu : 0 < u) :
    ∫ x, llrAddConst μ ν u x ∂μ ≤ (⨆ u' : {v // (0 : ℝ) < v},
      ∫ x, llrAddConst μ ν u' x ∂μ - log (∫ x, exp (llrAddConst μ ν u' x) ∂ν)) + log (1 + u) := by
  calc ∫ x, llrAddConst μ ν u x ∂μ
    = ∫ x, llrAddConst μ ν u x ∂μ - log (∫ x, exp (llrAddConst μ ν u x) ∂ν)
      + log (∫ x, exp (llrAddConst μ ν u x) ∂ν) := by abel
  _ ≤ (⨆ u : {v // (0 : ℝ) < v},
        ∫ x, llrAddConst μ ν u x ∂μ - log (∫ x, exp (llrAddConst μ ν u x) ∂ν))
      + log (∫ x, exp (llrAddConst μ ν u x) ∂ν) := by
        refine add_le_add ?_ le_rfl
        refine le_ciSup_of_le ?_ ⟨u, hu⟩ le_rfl
        refine ⟨klReal μ ν, fun y ⟨u, huy⟩ ↦ ?_⟩
        rw [← huy]
        exact integral_sub_log_integral_exp_le_klReal hμν h_int (llrAddConst μ ν _)
          (integrable_llrAddConst u.2.le h_int) (integrable_exp_llrAddConst u.2)
  _ = (⨆ u : {v // (0 : ℝ) < v},
        ∫ x, llrAddConst μ ν u x ∂μ - log (∫ x, exp (llrAddConst μ ν u x) ∂ν))
      + log (1 + u) := by rw [log_integral_exp_llrAddConst hμν hu]

lemma klReal_le_ciSup_integral_llrAddConst_sub [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    klReal μ ν ≤ ⨆ u : {v // (0 : ℝ) < v},
      ∫ x, llrAddConst μ ν u x ∂μ - log (∫ x, exp (llrAddConst μ ν u x) ∂ν) := by
  have h_bdd : BddBelow (Set.range fun u : {v // (0 : ℝ) < v} ↦ log (1 + u)) := by
    refine ⟨0, fun y ⟨u, huy⟩ ↦ ?_⟩
    rw [← huy]
    refine log_nonneg ?_
    simp [u.2.le]
  calc klReal μ ν
    ≤ ⨅ u : {v // (0 : ℝ) < v}, ∫ x, llrAddConst μ ν u x ∂μ :=
        klReal_le_ciInf_integral_llrAddConst hμν h_int
  _ ≤ ⨅ u : {v // (0 : ℝ) < v}, (⨆ u' : {v // (0 : ℝ) < v},
      ∫ x, llrAddConst μ ν u' x ∂μ - log (∫ x, exp (llrAddConst μ ν u' x) ∂ν)) + log (1 + u) := by
        refine ciInf_mono ?_ ?_
        · refine ⟨klReal μ ν, fun y ⟨u, huy⟩ ↦ ?_⟩
          rw [← huy]
          exact klReal_le_integral_llrAddConst u.2.le hμν h_int
        · exact fun u ↦ integral_llrAddConst_le_ciSup_add hμν h_int u.2
  _ = (⨆ u' : {v // (0 : ℝ) < v},
        ∫ x, llrAddConst μ ν u' x ∂μ - log (∫ x, exp (llrAddConst μ ν u' x) ∂ν))
      + ⨅ u : {v // (0 : ℝ) < v}, log (1 + u) := by
        rw [← add_ciInf h_bdd]
  _ = ⨆ u : {v // (0 : ℝ) < v},
      ∫ x, llrAddConst μ ν u x ∂μ - log (∫ x, exp (llrAddConst μ ν u x) ∂ν) := by
        suffices ⨅ (u : {v // (0 : ℝ) < v}), log (1 + u) = 0 by
          rw [this, add_zero]
        apply le_antisymm
        · refine le_of_forall_pos_le_add (fun ε hε ↦ ?_)
          exact ciInf_le_of_le h_bdd ⟨exp ε - 1, by simp [hε]⟩ (by simp)
        · refine le_ciInf (fun u ↦ log_nonneg ?_)
          simp [u.2.le]

/-- One side of the Donsker-Varadhan variational formula for the Kullback-Leibler divergence.
See `klReal_eq_ciSup` for the equality. -/
lemma klReal_le_ciSup [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    klReal μ ν ≤ ⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) := by
  refine (klReal_le_ciSup_integral_llrAddConst_sub hμν h_int).trans ?_
  refine ciSup_le (fun u ↦ ?_)
  refine le_ciSup_of_le ?_ (llrAddConst μ ν u) ?_
  · refine ⟨klReal μ ν, fun x ⟨f, hf⟩ ↦ ?_⟩
    rw [← hf]
    by_cases hfμ : Integrable f μ
    · simp only [hfμ, ciSup_unique]
      by_cases hf : Integrable (fun x ↦ exp (f x)) ν
      · simp only [hf, ciSup_unique]
        exact integral_sub_log_integral_exp_le_klReal hμν h_int f hfμ hf
      · simp only [hf, ciSup_empty]
        exact klReal_nonneg hμν
    · simp only [hfμ, ciSup_empty]
      exact klReal_nonneg hμν
  · simp [integrable_llrAddConst u.2.le h_int, integrable_exp_llrAddConst u.2]

/-- **Donsker-Varadhan** variational formula for the Kullback-Leibler divergence. -/
theorem klReal_eq_ciSup [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    klReal μ ν = ⨆ (f : α → ℝ) (_ : Integrable f μ) (_ : Integrable (fun x ↦ exp (f x)) ν),
        ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) :=
  le_antisymm (klReal_le_ciSup hμν h_int) (ciSup_le_klReal hμν h_int)

end MeasureTheory
