/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Kullback-Leibler divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

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

lemma toReal_kl [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ≪ ν)
    (h_int : Integrable (llr μ ν) μ) :
    (kl μ ν).toReal = ∫ a, llr μ ν a ∂μ + (ν univ).toReal - (μ univ).toReal := by
  rw [kl_of_ac_of_integrable h h_int, ENNReal.toReal_ofReal]
  exact integral_llr_add_sub_measure_univ_nonneg h h_int

/-- If `μ ≪ ν` and `μ univ = ν univ`, then `toReal` of the Kullback-Leibler divergence is equal to
an integral, without any integrability condition. -/
lemma toReal_kl_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : μ ≪ ν)
    (h_eq : μ univ = ν univ) :
    (kl μ ν).toReal = ∫ a, llr μ ν a ∂μ := by
  by_cases h_int : Integrable (llr μ ν) μ
  · simp [toReal_kl h h_int, h_eq]
  · rw [kl_of_not_integrable h_int, integral_undef h_int]
    simp [h_eq]

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

lemma kl_ne_top_iff : kl μ ν ≠ ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ := by
  rw [ne_eq, kl_eq_top_iff]
  push_neg
  rfl

open Classical in
lemma kl_eq_integral_klFun [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ ν = if μ ≪ ν ∧ Integrable (llr μ ν) μ
      then ENNReal.ofReal (∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν)
      else ∞ :=
  if_ctx_congr Iff.rfl (fun h ↦ by rw [integral_klFun_rnDeriv h.1 h.2]) fun _ ↦ rfl

section kl_nonneg

lemma kl_ge_mul_log (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ENNReal.ofReal ((μ univ).toReal * log ((μ univ).toReal / (ν univ).toReal)
        + (ν univ).toReal - (μ univ).toReal)
      ≤ kl μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [h_int]
  rw [kl_of_ac_of_integrable hμν h_int]
  exact ENNReal.ofReal_le_ofReal (kl_ge_mul_log' hμν h_int)

/-- **Converse Gibbs' inequality**: the Kullback-Leibler divergence between two finite measures is
zero if and only if the two measures are equal. -/
lemma kl_eq_zero_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    kl μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ kl_self _⟩
  by_cases hμν : μ ≪ ν
  swap; · rw [kl_of_not_ac hμν] at h; exact (ENNReal.top_ne_zero h).elim
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · rw [kl_of_not_integrable h_int] at h; exact (ENNReal.top_ne_zero h).elim
  simp only [kl_of_ac_of_integrable hμν h_int, ENNReal.ofReal_eq_zero] at h
  rw [← integral_klFun_rnDeriv hμν h_int] at h
  have h' : ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν = 0 :=
    le_antisymm h (integral_nonneg fun x ↦ klFun_nonneg ENNReal.toReal_nonneg)
  rw [integral_eq_zero_iff_of_nonneg] at h'
  rotate_left
  · exact fun _ ↦ klFun_nonneg ENNReal.toReal_nonneg
  · rwa [integrable_klFun_rnDeriv_iff hμν]
  refine (Measure.rnDeriv_eq_one_iff_eq hμν).mp ?_
  filter_upwards [h'] with x hx
  rwa [Pi.zero_apply, klFun_eq_zero_iff ENNReal.toReal_nonneg, ENNReal.toReal_eq_one_iff] at hx

-- /-- **Gibbs' inequality**: the Kullback-Leibler divergence between two probability distributions
-- is nonnegative.
-- Our definition of `kl` is nonnegative since it has type `ℝ≥0∞`. -/
-- lemma kl_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
--     0 ≤ kl μ ν := kl_nonneg' μ ν (by simp)

end kl_nonneg

end ProbabilityTheory
