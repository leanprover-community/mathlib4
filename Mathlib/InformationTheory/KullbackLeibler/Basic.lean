/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.MeasureTheory.Decomposition.IntegralRNDeriv

/-!
# Kullback-Leibler divergence

The Kullback-Leibler divergence is a measure of the difference between two measures.

## Main definitions

* `kl μ ν`: Kullback-Leibler divergence between two measures, with value in `ℝ≥0∞`,
  defined as `∞` if `μ` is not absolutely continuous with respect to `ν` or
  if the log-likelihood ratio `llr μ ν` is not integrable, and by
  `ENNReal.ofReal (∫ x, llr μ ν x ∂μ + (ν univ).toReal - (μ univ).toReal)` otherwise.

Note that our Kullback-Leibler divergence is nonnegative by definition (it takes value in `ℝ≥0∞`).
However `∫ x, llr μ ν x ∂μ + (ν univ).toReal - (μ univ).toReal` is nonnegative for all finite
measures `μ ≪ ν`, as proved in the lemma `integral_llr_add_sub_measure_univ_nonneg`.
That lemma is our version of Gibbs' inequality ("the Kullback-Leibler divergence is nonnegative").

## Main statements

* `kl_eq_zero_iff` : the Kullback-Leibler divergence between two finite measures is zero if and only
  if the two measures are equal.

-/

open Real MeasureTheory Filter MeasurableSpace Set

open scoped ENNReal NNReal Topology BigOperators

namespace ProbabilityTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

open Classical in
/-- Kullback-Leibler divergence between two measures. -/
noncomputable def kl (μ ν : Measure α) : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ
    then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + (ν univ).toReal - (μ univ).toReal)
    else ∞

lemma kl_of_ac_of_integrable (h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) :
    kl μ ν = ENNReal.ofReal (∫ x, llr μ ν x ∂μ + (ν univ).toReal - (μ univ).toReal) :=
  if_pos ⟨h1, h2⟩

@[simp]
lemma kl_of_not_ac (h : ¬ μ ≪ ν) : kl μ ν = ∞ := if_neg (not_and_of_not_left _ h)

@[simp]
lemma kl_of_not_integrable (h : ¬ Integrable (llr μ ν) μ) : kl μ ν = ∞ :=
  if_neg (not_and_of_not_right _ h)

@[simp]
lemma kl_self (μ : Measure α) [SigmaFinite μ] : kl μ μ = 0 := by
  have h := llr_self μ
  rw [kl, if_pos]
  · simp [integral_congr_ae h]
  · rw [integrable_congr h]
    exact ⟨Measure.AbsolutelyContinuous.rfl, integrable_zero _ _ μ⟩

@[simp]
lemma kl_zero_left [IsFiniteMeasure ν] : kl 0 ν = ν univ := by
  convert kl_of_ac_of_integrable (Measure.AbsolutelyContinuous.zero _) integrable_zero_measure
  simp [integral_zero_measure, EReal.coe_zero]

@[simp]
lemma kl_zero_right [NeZero μ] : kl μ 0 = ∞ :=
  kl_of_not_ac (Measure.absolutelyContinuous_zero_iff.mp.mt (NeZero.ne _))

lemma kl_eq_top_iff : kl μ ν = ∞ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  constructor <;> intro h <;> push_neg at *
  · contrapose! h
    rw [kl_of_ac_of_integrable h.1 h.2]
    simp only [ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
  · rcases or_not_of_imp h with (h | h) <;> simp [h]

lemma kl_ne_top_iff : kl μ ν ≠ ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ := by simp [ne_eq, kl_eq_top_iff]

section AlternativeFormulas

open Classical in
lemma kl_eq_integral_klFun [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ
      then ENNReal.ofReal (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν)
      else ∞ :=
  if_ctx_congr Iff.rfl (fun h ↦ by rw [integral_klFun_rnDeriv h.1 h.2]) fun _ ↦ rfl

open Classical in
lemma kl_eq_lintegral_klFun [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ ν = if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν else ∞ := by
  rw [kl_eq_integral_klFun]
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  have h_int_iff := lintegral_ofReal_ne_top_iff_integrable
    (f := fun x ↦ klFun (μ.rnDeriv ν x).toReal) (μ := ν) ?_ ?_
  rotate_left
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg
  by_cases h_int : Integrable (llr μ ν) μ
  · simp only [hμν, h_int, and_self, ↓reduceIte]
    rw [ofReal_integral_eq_lintegral_ofReal]
    · rwa [integrable_klFun_rnDeriv_iff hμν]
    · exact ae_of_all _ fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg
  · rw [← not_iff_not] at h_int_iff
    simp only [ne_eq, Decidable.not_not] at h_int_iff
    symm
    simp [hμν, h_int, h_int_iff, integrable_klFun_rnDeriv_iff hμν]

end AlternativeFormulas

section Real

/-- **Gibbs' inequality**: the Kullback-Leibler divergence is nonnegative.
Note that since `kl` takes value in `ℝ≥0∞` (defined when it is finite as `ENNReal.ofReal (...)`),
it is nonnegative by definition. This lemma proves that the argument of `ENNReal.ofReal`
is also nonnegative. -/
lemma integral_llr_add_sub_measure_univ_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    0 ≤ ∫ x, llr μ ν x ∂μ + (ν univ).toReal - (μ univ).toReal := by
  rw [← integral_klFun_rnDeriv hμν h_int]
  exact integral_nonneg fun x ↦ klFun_nonneg ENNReal.toReal_nonneg

lemma toReal_kl [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    (kl μ ν).toReal = ∫ a, llr μ ν a ∂μ + (ν univ).toReal - (μ univ).toReal := by
  rw [kl_of_ac_of_integrable h h_int, ENNReal.toReal_ofReal]
  exact integral_llr_add_sub_measure_univ_nonneg h h_int

/-- If `μ ≪ ν` and `μ univ = ν univ`, then `toReal` of the Kullback-Leibler divergence is equal to
an integral, without any integrability condition. -/
lemma toReal_kl_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ≪ ν) (h_eq : μ univ = ν univ) :
    (kl μ ν).toReal = ∫ a, llr μ ν a ∂μ := by
  by_cases h_int : Integrable (llr μ ν) μ
  · simp [toReal_kl h h_int, h_eq]
  · rw [kl_of_not_integrable h_int, integral_undef h_int]
    simp [h_eq]

end Real

section Inequalities

lemma integral_llr_add_mul_log_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    0 ≤ ∫ x, llr μ ν x ∂μ + (μ univ).toReal * log (ν univ).toReal + 1 - (μ univ).toReal := by
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  have : NeZero ν := ⟨hν⟩
  let ν' := (ν univ)⁻¹ • ν
  have hμν' : μ ≪ ν' := hμν.trans (Measure.absolutelyContinuous_smul (by simp))
  have h := integral_llr_add_sub_measure_univ_nonneg hμν' ?_
  swap
  · rw [integrable_congr (llr_smul_right hμν (ν univ)⁻¹ (by simp) (by simp [hν]))]
    exact h_int.sub (integrable_const _)
  rw [integral_congr_ae (llr_smul_right hμν (ν univ)⁻¹ (by simp) (by simp [hν])),
    integral_sub h_int (integrable_const _), integral_const, smul_eq_mul] at h
  simpa using h

lemma mul_log_le_toReal_kl [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    (μ univ).toReal * log ((μ univ).toReal / (ν univ).toReal) + (ν univ).toReal - (μ univ).toReal
      ≤ (kl μ ν).toReal := by
  rw [toReal_kl hμν h_int]
  by_cases hμ : μ = 0
  · simp [hμ]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  simp only [tsub_le_iff_right, sub_add_cancel, add_le_add_iff_right]
  rw [← integral_rnDeriv_mul_log hμν]
  refine (le_of_eq ?_).trans
    (mul_le_integral_rnDeriv_of_ac (f := fun x ↦ x * log x) convexOn_mul_log ?_ ?_ hμν)
  · rw [← mul_assoc]
    congr 1
    rw [div_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀, one_mul]
    simp [ENNReal.toReal_eq_zero_iff, hν]
  · exact Continuous.continuousOn (by fun_prop)
  · rwa [integrable_rnDeriv_mul_log_iff hμν]

lemma mul_log_le_kl (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal ((μ univ).toReal * log ((μ univ).toReal / (ν univ).toReal)
        + (ν univ).toReal - (μ univ).toReal)
      ≤ kl μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [h_int]
  rw [← ENNReal.ofReal_toReal (a := kl μ ν)]
  · exact ENNReal.ofReal_le_ofReal (mul_log_le_toReal_kl hμν h_int)
  · rw [kl_ne_top_iff]
    exact ⟨hμν, h_int⟩

end Inequalities

/-- **Converse Gibbs' inequality**: the Kullback-Leibler divergence between two finite measures is
zero if and only if the two measures are equal. -/
lemma kl_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ kl_self _⟩
  by_cases hμν : μ ≪ ν
  swap; · rw [kl_of_not_ac hμν] at h; exact (ENNReal.top_ne_zero h).elim
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · rw [kl_of_not_integrable h_int] at h; exact (ENNReal.top_ne_zero h).elim
  simp only [kl_eq_lintegral_klFun, hμν, ↓reduceIte] at h
  rw [lintegral_eq_zero_iff (by fun_prop)] at h
  refine (Measure.rnDeriv_eq_one_iff_eq hμν).mp ?_
  filter_upwards [h] with x hx
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
  have hx' : klFun (μ.rnDeriv ν x).toReal = 0 := le_antisymm hx (klFun_nonneg ENNReal.toReal_nonneg)
  rwa [klFun_eq_zero_iff ENNReal.toReal_nonneg, ENNReal.toReal_eq_one_iff] at hx'

end ProbabilityTheory
