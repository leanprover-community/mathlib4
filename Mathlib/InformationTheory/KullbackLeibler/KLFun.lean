/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio

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

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {x : ℝ}

lemma le_integral_rnDeriv_of_ac [IsFiniteMeasure μ] [IsProbabilityMeasure ν] {f : ℝ → ℝ}
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (hf_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν)
    (hμν : μ ≪ ν) :
    f (μ univ).toReal ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
  calc f (μ univ).toReal
    = f (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp)
      Measure.integrable_toReal_rnDeriv hf_int

lemma mul_le_integral_rnDeriv_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : ℝ → ℝ}
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (hf_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν)
    (hμν : μ ≪ ν) :
    (ν univ).toReal * f ((μ univ).toReal / (ν univ).toReal)
      ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
  by_cases hν : ν = 0
  · simp [hν]
  have : NeZero ν := ⟨hν⟩
  let μ' := (ν univ)⁻¹ • μ
  let ν' := (ν univ)⁻¹ • ν
  have : IsFiniteMeasure μ' := μ.smul_finite (by simp [hν])
  have hμν' : μ' ≪ ν' := hμν.smul _
  have h_rnDeriv_eq : μ'.rnDeriv ν' =ᵐ[ν] μ.rnDeriv ν := by
    have h1' : μ'.rnDeriv ν' =ᵐ[ν'] (ν univ)⁻¹ • μ.rnDeriv ν' :=
      Measure.rnDeriv_smul_left_of_ne_top' (μ := ν') (ν := μ) (by simp [hν])
    have h1 : μ'.rnDeriv ν' =ᵐ[ν] (ν univ)⁻¹ • μ.rnDeriv ν' := by
      rwa [Measure.ae_smul_measure_eq] at h1'
      simp
    have h2 : μ.rnDeriv ν' =ᵐ[ν] (ν univ)⁻¹⁻¹ • μ.rnDeriv ν :=
      Measure.rnDeriv_smul_right_of_ne_top' (μ := ν) (ν := μ) (by simp) (by simp [hν])
    filter_upwards [h1, h2] with x h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
    simp only [inv_inv, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
    · simp [hν]
    · simp
  have h_eq : ∫ x, f (μ'.rnDeriv ν' x).toReal ∂ν'
      = (ν univ).toReal⁻¹ * ∫ x, f ((μ.rnDeriv ν x).toReal) ∂ν := by
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [h_rnDeriv_eq] with x hx
    rw [hx]
  have h : f (μ' univ).toReal ≤ ∫ x, f (μ'.rnDeriv ν' x).toReal ∂ν' :=
    le_integral_rnDeriv_of_ac hf_cvx hf_cont ?_ hμν'
  swap
  · refine Integrable.smul_measure ?_ (by simp [hν])
    refine (integrable_congr ?_).mpr hf_int
    filter_upwards [h_rnDeriv_eq] with x hx
    rw [hx]
  rw [h_eq, mul_comm, ← div_le_iff₀, div_eq_inv_mul, inv_inv] at h
  · convert h
    · simp only [div_eq_inv_mul, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv, μ']
  · simp [ENNReal.toReal_pos_iff, hν]

section MulLog

lemma integrable_rnDeriv_mul_log_iff [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    Integrable (fun a ↦ (μ.rnDeriv ν a).toReal * log (μ.rnDeriv ν a).toReal) ν
      ↔ Integrable (llr μ ν) μ :=
  integrable_rnDeriv_smul_iff hμν

lemma integral_rnDeriv_mul_log [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) :
    ∫ a, (μ.rnDeriv ν a).toReal * log (μ.rnDeriv ν a).toReal ∂ν = ∫ a, llr μ ν a ∂μ := by
  simp_rw [← smul_eq_mul]
  rw [integral_rnDeriv_smul hμν]
  rfl

@[simp]
lemma rightDeriv_mul_log (hx : x ≠ 0) : derivWithin (fun x ↦ x * log x) (Ioi x) x = log x + 1 :=
  (Real.hasDerivAt_mul_log hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

@[simp]
lemma leftDeriv_mul_log (hx : x ≠ 0) : derivWithin (fun x ↦ x * log x) (Iio x) x = log x + 1 :=
  (Real.hasDerivAt_mul_log hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)

lemma tendsto_rightDeriv_mul_log_atTop :
    Tendsto (fun x ↦ derivWithin (fun x ↦ x * log x) (Ioi x) x) atTop atTop := by
  have h_tendsto : Tendsto (fun x ↦ log x + 1) atTop atTop :=
    tendsto_log_atTop.atTop_add tendsto_const_nhds
  refine (tendsto_congr' ?_).mpr h_tendsto
  rw [EventuallyEq, eventually_atTop]
  exact ⟨1, fun _ hx ↦ rightDeriv_mul_log (zero_lt_one.trans_le hx).ne'⟩

/-- The Kullback-Leibler divergence is an f-divergence for this function. -/
noncomputable abbrev klFun (x : ℝ) : ℝ := x * log x + 1 - x

lemma klFun_one : klFun 1 = 0 := by simp

lemma strictConvexOn_klFun : StrictConvexOn ℝ (Ici 0) klFun := by
  unfold klFun
  simp_rw [add_sub_assoc]
  refine strictConvexOn_mul_log.add_convexOn ?_
  exact (convexOn_const _ (convex_Ici _)).sub (concaveOn_id (convex_Ici _))

lemma convexOn_klFun : ConvexOn ℝ (Ici 0) klFun := strictConvexOn_klFun.convexOn

lemma hasDerivAt_klFun (hx : x ≠ 0) : HasDerivAt klFun (log x) x := by
  convert ((hasDerivAt_mul_log hx).add (hasDerivAt_const x 1)).sub (hasDerivAt_id x) using 1
  ring

@[simp]
lemma deriv_klFun (hx : x ≠ 0) : deriv klFun x = log x := (hasDerivAt_klFun hx).deriv

@[simp]
lemma rightDeriv_klFun (hx : x ≠ 0) : derivWithin klFun (Ioi x) x = log x :=
  (hasDerivAt_klFun hx).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)

lemma rightDeriv_klFun_one : derivWithin klFun (Ioi 1) 1 = 0 := by simp

lemma rightDeriv_klFun_eventually_eq : (fun x ↦ derivWithin klFun (Ioi x) x) =ᶠ[atTop] log := by
  filter_upwards [eventually_ne_atTop 0] with x hx
  rw [rightDeriv_klFun hx]

lemma tendsto_rightDeriv_klFun_atTop :
    Tendsto (fun x ↦ derivWithin klFun (Ioi x) x) atTop atTop := by
  rw [tendsto_congr' rightDeriv_klFun_eventually_eq]
  exact tendsto_log_atTop

lemma klFun_nonneg (hx : 0 ≤ x) : 0 ≤ klFun x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  · rw [← klFun_one]
    refine ConvexOn.ge_of_rightDeriv_eq_zero (S := Ioi 0) ?_ (by simp) (by simp)  hx
    exact convexOn_klFun.subset (Ioi_subset_Ici le_rfl) (convex_Ioi _)

lemma klFun_eq_zero_iff (hx : 0 ≤ x) : klFun x = 0 ↔ x = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  exact strictConvexOn_klFun.eq_of_isMinOn (isMinOn_iff.mpr fun y hy ↦ h ▸ klFun_nonneg hy)
    (isMinOn_iff.mpr fun y hy ↦ klFun_one ▸ klFun_nonneg hy) hx (zero_le_one' ℝ)

lemma tendsto_klFun_atTop : Tendsto klFun atTop atTop := by
  have : klFun = (fun x ↦ x * (log x - 1) + 1) := by ext; ring
  rw [this]
  refine Tendsto.atTop_add ?_ tendsto_const_nhds
  refine Tendsto.atTop_mul_atTop ?_ ?_
  · exact fun _ s ↦ s
  · exact tendsto_log_atTop.atTop_add tendsto_const_nhds

lemma continuous_klFun : Continuous klFun := by fun_prop

lemma integrable_klFun_iff [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hμν : μ ≪ ν) :
    Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν ↔ Integrable (llr μ ν) μ := by
  suffices Integrable (fun x ↦ (μ.rnDeriv ν x).toReal * log (μ.rnDeriv ν x).toReal
      + (1 - (μ.rnDeriv ν x).toReal)) ν ↔ Integrable (llr μ ν) μ by
    convert this using 3 with x
    rw [klFun, add_sub_assoc]
  rw [integrable_add_iff_integrable_left']
  · rw [integrable_rnDeriv_mul_log_iff hμν]
  · exact (integrable_const _).sub Measure.integrable_toReal_rnDeriv

end MulLog

lemma integral_klFun_rnDeriv [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    ∫ x, klFun (μ.rnDeriv ν x).toReal ∂ν
      = ∫ x, llr μ ν x ∂μ + (ν univ).toReal - (μ univ).toReal := by
  rw [integral_sub, integral_add, integral_const, Measure.integral_toReal_rnDeriv hμν, smul_eq_mul,
    mul_one]
  · congr 2
    exact integral_rnDeriv_smul hμν
  · rwa [integrable_rnDeriv_mul_log_iff hμν]
  · exact integrable_const _
  · refine Integrable.add ?_ (integrable_const _)
    rwa [integrable_rnDeriv_mul_log_iff hμν]
  · exact Measure.integrable_toReal_rnDeriv

lemma integral_llr_add_sub_measure_univ_nonneg [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    0 ≤ ∫ x, llr μ ν x ∂μ + (ν univ).toReal - (μ univ).toReal := by
  rw [← integral_klFun_rnDeriv hμν h_int]
  exact integral_nonneg fun x ↦ klFun_nonneg ENNReal.toReal_nonneg

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
  have hμν' : μ ≪ ν' :=
    Measure.AbsolutelyContinuous.trans hμν (Measure.absolutelyContinuous_smul (by simp))
  have h := integral_llr_add_sub_measure_univ_nonneg hμν' ?_
  swap
  · rw [integrable_congr (llr_smul_right hμν (ν univ)⁻¹ (by simp) (by simp [hν]))]
    exact h_int.sub (integrable_const _)
  rw [integral_congr_ae (llr_smul_right hμν (ν univ)⁻¹ (by simp) (by simp [hν]))] at h
  rw [integral_sub h_int (integrable_const _), integral_const, smul_eq_mul] at h
  simp only [ENNReal.toReal_inv, log_inv, mul_neg, sub_neg_eq_add, measure_univ, ENNReal.one_toReal]
    at h
  exact h

lemma kl_ge_mul_log' [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (h_int : Integrable (llr μ ν) μ) :
    (μ univ).toReal * log ((μ univ).toReal / (ν univ).toReal) + (ν univ).toReal - (μ univ).toReal
      ≤ ∫ x, llr μ ν x ∂μ + (ν univ).toReal - (μ univ).toReal := by
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

end ProbabilityTheory
