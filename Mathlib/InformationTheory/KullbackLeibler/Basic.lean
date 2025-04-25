/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-!
# Kullback-Leibler divergence

The Kullback-Leibler divergence is a measure of the difference between two measures.

## Main definitions

* `klDiv μ ν`: Kullback-Leibler divergence between two measures, with value in `ℝ≥0∞`,
  defined as `∞` if `μ` is not absolutely continuous with respect to `ν` or
  if the log-likelihood ratio `llr μ ν` is not integrable with respect to `μ`, and by
  `ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real - μ.real univ)` otherwise.

Note that our Kullback-Leibler divergence is nonnegative by definition (it takes value in `ℝ≥0∞`).
However `∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ` is nonnegative for all finite
measures `μ ≪ ν`, as proved in the lemma `integral_llr_add_sub_measure_univ_nonneg`.
That lemma is our version of Gibbs' inequality ("the Kullback-Leibler divergence is nonnegative").

## Main statements

* `klDiv_eq_zero_iff` : the Kullback-Leibler divergence between two finite measures is zero if and
  only if the two measures are equal.

## Implementation details

The Kullback-Leibler divergence on probability measures is `∫ x, llr μ ν x ∂μ` if `μ ≪ ν`
(and the log-likelihood ratio is integrable) and `∞` otherwise.
The definition we use extends this to finite measures by introducing a correction term
`ν.real univ - μ.real univ`. The definition of the divergence thus uses the formula
`∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ`, which is nonnegative for all finite
measures `μ ≪ ν`. This also makes `klDiv μ ν` equal to an f-divergence: it equals the integral
`∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν`, in which `klFun x = x * log x + 1 - x`.

-/

open Real MeasureTheory Set

open scoped ENNReal

namespace InformationTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

open Classical in
/-- Kullback-Leibler divergence between two measures. -/
noncomputable irreducible_def klDiv (μ ν : Measure α) : ℝ≥0∞ :=
  if μ ≪ ν ∧ Integrable (llr μ ν) μ
    then ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ)
    else ∞

lemma klDiv_of_ac_of_integrable (h1 : μ ≪ ν) (h2 : Integrable (llr μ ν) μ) :
    klDiv μ ν = ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ) := by
  rw [klDiv_def]
  exact if_pos ⟨h1, h2⟩

@[simp]
lemma klDiv_of_not_ac (h : ¬ μ ≪ ν) : klDiv μ ν = ∞ := by
  rw [klDiv_def]
  exact if_neg (not_and_of_not_left _ h)

@[simp]
lemma klDiv_of_not_integrable (h : ¬ Integrable (llr μ ν) μ) : klDiv μ ν = ∞ := by
  rw [klDiv_def]
  exact if_neg (not_and_of_not_right _ h)

@[simp]
lemma klDiv_self (μ : Measure α) [SigmaFinite μ] : klDiv μ μ = 0 := by
  have h := llr_self μ
  rw [klDiv_def, if_pos]
  · simp [integral_congr_ae h]
  · rw [integrable_congr h]
    exact ⟨Measure.AbsolutelyContinuous.rfl, integrable_zero _ _ μ⟩

@[simp]
lemma klDiv_zero_left [IsFiniteMeasure ν] : klDiv 0 ν = ν univ := by
  convert klDiv_of_ac_of_integrable (Measure.AbsolutelyContinuous.zero _) integrable_zero_measure
  simp

@[simp]
lemma klDiv_zero_right [NeZero μ] : klDiv μ 0 = ∞ :=
  klDiv_of_not_ac (Measure.absolutelyContinuous_zero_iff.mp.mt (NeZero.ne _))

lemma klDiv_eq_top_iff : klDiv μ ν = ∞ ↔ μ ≪ ν → ¬ Integrable (llr μ ν) μ := by
  constructor <;> intro h
  · contrapose! h
    simp [klDiv_of_ac_of_integrable h.1 h.2]
  · rcases or_not_of_imp h with (h | h) <;> simp [h]

lemma klDiv_ne_top_iff : klDiv μ ν ≠ ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ := by
  simp [ne_eq, klDiv_eq_top_iff]

section AlternativeFormulas

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

open Classical in
lemma klDiv_eq_integral_klFun :
    klDiv μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ
      then ENNReal.ofReal (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν)
      else ∞ := by
  rw [klDiv_def]
  exact if_ctx_congr Iff.rfl (fun h ↦ by rw [integral_klFun_rnDeriv h.1 h.2]) fun _ ↦ rfl

open Classical in
lemma klDiv_eq_lintegral_klFun :
    klDiv μ ν = if μ ≪ ν then ∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν else ∞ := by
  rw [klDiv_eq_integral_klFun]
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
  · rw [← not_iff_not, ne_eq, Decidable.not_not] at h_int_iff
    symm
    simp [hμν, h_int, h_int_iff, integrable_klFun_rnDeriv_iff hμν]

end AlternativeFormulas

section Real

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- **Gibbs' inequality**: the Kullback-Leibler divergence is nonnegative.
Note that since `klDiv` takes value in `ℝ≥0∞` (defined when it is finite as `ENNReal.ofReal (...)`),
it is nonnegative by definition. This lemma proves that the argument of `ENNReal.ofReal`
is also nonnegative. -/
lemma integral_llr_add_sub_measure_univ_nonneg (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    0 ≤ ∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ := by
  rw [← integral_klFun_rnDeriv hμν h_int]
  exact integral_nonneg fun x ↦ klFun_nonneg ENNReal.toReal_nonneg

lemma toReal_klDiv (h : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ + ν.real univ - μ.real univ := by
  rw [klDiv_of_ac_of_integrable h h_int, ENNReal.toReal_ofReal]
  exact integral_llr_add_sub_measure_univ_nonneg h h_int

/-- If `μ ≪ ν` and `μ univ = ν univ`, then `toReal` of the Kullback-Leibler divergence is equal to
an integral, without any integrability condition. -/
lemma toReal_klDiv_of_measure_eq (h : μ ≪ ν) (h_eq : μ univ = ν univ) :
    (klDiv μ ν).toReal = ∫ a, llr μ ν a ∂μ := by
  by_cases h_int : Integrable (llr μ ν) μ
  · simp [toReal_klDiv h h_int, h_eq, measureReal_def]
  · rw [klDiv_of_not_integrable h_int, integral_undef h_int, ENNReal.toReal_top]

lemma toReal_klDiv_eq_integral_klFun (h : μ ≪ ν) :
    (klDiv μ ν).toReal = ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν := by
  by_cases h_int : Integrable (llr μ ν) μ
  · rw [klDiv_eq_integral_klFun, if_pos ⟨h, h_int⟩, ENNReal.toReal_ofReal]
    exact integral_nonneg fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg
  · rw [integral_undef]
    · rw [klDiv_of_not_integrable h_int, ENNReal.toReal_top]
    · rwa [integrable_klFun_rnDeriv_iff h]

end Real

section Inequalities

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

lemma integral_llr_add_mul_log_nonneg (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    0 ≤ ∫ x, llr μ ν x ∂μ + μ.real univ * log (ν.real univ) + 1 - μ.real univ := by
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

lemma mul_klFun_le_toReal_klDiv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ν.real univ * klFun (μ.real univ / ν.real univ) ≤ (klDiv μ ν).toReal := by
  calc ν.real univ * klFun (μ.real univ / ν.real univ)
  _ ≤ ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν := by
    refine mul_le_integral_rnDeriv_of_ac convexOn_klFun continuous_klFun.continuousWithinAt ?_ hμν
    rwa [integrable_klFun_rnDeriv_iff hμν]
  _ = (klDiv μ ν).toReal := by rw [toReal_klDiv_eq_integral_klFun hμν]

lemma mul_log_le_toReal_klDiv (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    μ.real univ * log (μ.real univ / ν.real univ) + ν.real univ - μ.real univ
      ≤ (klDiv μ ν).toReal := by
  by_cases hμ : μ = 0
  · simp [hμ, measureReal_def]
  by_cases hν : ν = 0
  · refine absurd ?_ hμ
    rw [hν] at hμν
    exact Measure.absolutelyContinuous_zero_iff.mp hμν
  refine (le_of_eq ?_).trans (mul_klFun_le_toReal_klDiv hμν h_int)
  have : ν.real univ * (μ.real univ / ν.real univ) = μ.real univ := by
    rw [mul_div_cancel₀]; simp [ENNReal.toReal_eq_zero_iff, hν, measureReal_def]
  rw [klFun, mul_sub, mul_add, mul_one, ← mul_assoc, this]

lemma mul_log_le_klDiv (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal (μ.real univ * log (μ.real univ / ν.real univ)
        + ν.real univ - μ.real univ)
      ≤ klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [h_int]
  rw [← ENNReal.ofReal_toReal (a := klDiv μ ν)]
  · exact ENNReal.ofReal_le_ofReal (mul_log_le_toReal_klDiv hμν h_int)
  · rw [klDiv_ne_top_iff]
    exact ⟨hμν, h_int⟩

end Inequalities

/-- **Converse Gibbs' inequality**: the Kullback-Leibler divergence between two finite measures is
zero if and only if the two measures are equal. -/
lemma klDiv_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ klDiv_self _⟩
  have h_ne : klDiv μ ν ≠ ⊤ := by simp [h]
  rw [klDiv_ne_top_iff] at h_ne
  rw [klDiv_eq_lintegral_klFun, if_pos h_ne.1, lintegral_eq_zero_iff (by fun_prop)] at h
  refine (Measure.rnDeriv_eq_one_iff_eq h_ne.1).mp ?_
  filter_upwards [h] with x hx
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hx
  have hx' : klFun (μ.rnDeriv ν x).toReal = 0 := le_antisymm hx (klFun_nonneg ENNReal.toReal_nonneg)
  rwa [klFun_eq_zero_iff ENNReal.toReal_nonneg, ENNReal.toReal_eq_one_iff] at hx'

end InformationTheory
