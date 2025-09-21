/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Integrals of functions of Radon-Nikodym derivatives

## Main statements

* `mul_le_integral_rnDeriv_of_ac`: for a convex continuous function `f` on `[0, ∞)`, if `μ`
  is absolutely continuous with respect to `ν`, then
  `ν.real univ * f (μ.real univ / ν.real univ) ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν`.

-/


open Set

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α} {f : ℝ → ℝ}

@[fun_prop]
lemma Measure.integrable_toReal_rnDeriv [IsFiniteMeasure μ] :
    Integrable (fun x ↦ (μ.rnDeriv ν x).toReal) ν :=
  integrable_toReal_of_lintegral_ne_top (Measure.measurable_rnDeriv _ _).aemeasurable
    (Measure.lintegral_rnDeriv_lt_top _ _).ne

/-- For a convex continuous function `f` on `[0, ∞)`, if `μ` is absolutely continuous
with respect to a probability measure `ν`, then
`f μ.real univ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν`. -/
lemma le_integral_rnDeriv_of_ac [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (hf_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) :
    f (μ.real univ) ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
  have hf_cont' : ContinuousOn f (Ici 0) := by
    intro x hx
    rcases eq_or_lt_of_le (α := ℝ) (hx : 0 ≤ x) with rfl | hx_pos
    · exact hf_cont
    · have h := hf_cvx.continuousOn_interior x
      simp only [nonempty_Iio, interior_Ici', mem_Ioi] at h
      rw [continuousWithinAt_iff_continuousAt (Ioi_mem_nhds hx_pos)] at h
      exact (h hx_pos).continuousWithinAt
  calc f (μ.real univ)
    = f (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont' isClosed_Ici (by simp)
      Measure.integrable_toReal_rnDeriv hf_int

/-- For a convex continuous function `f` on `[0, ∞)`, if `μ` is absolutely continuous
with respect to `ν`, then
`ν.real univ * f (μ.real univ / ν.real univ) ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν`. -/
lemma mul_le_integral_rnDeriv_of_ac [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousWithinAt f (Ici 0) 0)
    (hf_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) (hμν : μ ≪ ν) :
    ν.real univ * f (μ.real univ / ν.real univ)
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
      = (ν.real univ)⁻¹ * ∫ x, f ((μ.rnDeriv ν x).toReal) ∂ν := by
    rw [integral_smul_measure, smul_eq_mul, ENNReal.toReal_inv]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [h_rnDeriv_eq] with x hx
    rw [hx]
  have h : f (μ'.real univ) ≤ ∫ x, f (μ'.rnDeriv ν' x).toReal ∂ν' :=
    le_integral_rnDeriv_of_ac hf_cvx hf_cont ?_ hμν'
  swap
  · refine Integrable.smul_measure ?_ (by simp [hν])
    refine (integrable_congr ?_).mpr hf_int
    filter_upwards [h_rnDeriv_eq] with x hx
    rw [hx]
  rw [h_eq, mul_comm, ← div_le_iff₀, div_eq_inv_mul, inv_inv] at h
  · convert h
    · simp only [div_eq_inv_mul, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_inv, μ', measureReal_def]
  · simp [ENNReal.toReal_pos_iff, hν, measureReal_def]

end MeasureTheory
