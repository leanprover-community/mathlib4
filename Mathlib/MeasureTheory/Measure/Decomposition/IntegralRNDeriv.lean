/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.RadonNikodym

/-!
# Integrals of functions of Radon-Nikodym derivatives

## Main statements

* `mul_le_integral_rnDeriv_of_ac`: for a convex continuous function `f` on `[0, ∞)`, if `μ`
  is absolutely continuous with respect to `ν`, then
  `ν.real univ * f (μ.real univ / ν.real univ) ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν`.

-/

public section


open Set ProbabilityTheory

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
      rwa [Measure.ae_ennreal_smul_measure_eq] at h1'
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

section Integrable

variable {β : Type*} {mβ : MeasurableSpace β} {κ η : Kernel α β} {f g : ℝ → ℝ}

lemma _root_.ConvexOn.apply_rnDeriv_ae_le_integral [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (h_int : Integrable (fun p ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    (fun a ↦ f (μ.rnDeriv ν a).toReal)
      ≤ᵐ[ν] fun a ↦ ∫ b, f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b)).toReal ∂(η a) := by
  have h_compProd : (fun p ↦ μ.rnDeriv ν p.1 * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) p) =ᵐ[ν ⊗ₘ η]
      (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) := (rnDeriv_compProd hκη ν).symm
  have h_lt_top := Measure.ae_ae_of_ae_compProd <| (μ ⊗ₘ κ).rnDeriv_lt_top (ν ⊗ₘ η)
  have h_integrable := Measure.integrable_toReal_rnDeriv (μ := μ ⊗ₘ κ) (ν := ν ⊗ₘ η)
  rw [Measure.integrable_compProd_iff] at h_integrable h_int
  rotate_left
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  have h_ae1 : ∀ᵐ a ∂ν, μ.rnDeriv ν a * ∫⁻ b,
      (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) ∂(η a) = (μ.rnDeriv ν) a := by
    suffices ∀ᵐ a ∂ν, μ.rnDeriv ν a ≠ 0 → ∫⁻ b, (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) ∂(η a) = 1 by
      filter_upwards [this] with a ha
      by_cases h0 : μ.rnDeriv ν a = 0
      · simp [h0]
      · rw [ha h0, mul_one]
    refine Measure.ae_rnDeriv_ne_zero_imp_of_ae ?_
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (by fun_prop) measurable_const ?_
    intro s hs hsμ
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, one_mul]
    calc ∫⁻ a in s, ∫⁻ b, (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) ∂(η a) ∂μ
    _ = ∫⁻ a in s, ∫⁻ b in univ, (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) ∂(η a) ∂μ := by simp
    _ = μ s := by
      rw [← Measure.setLIntegral_compProd (by fun_prop) hs .univ, Measure.setLIntegral_rnDeriv hκη,
        Measure.compProd_apply_prod hs .univ]
      simp
  have h_ae2 : ∀ᵐ a ∂ν, ∀ᵐ b ∂(η a), μ.rnDeriv ν a * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) =
      (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b) := by
    rwa [Filter.EventuallyEq, Measure.ae_compProd_iff] at h_compProd
    simp only [measurableSet_setOf]
    fun_prop
  filter_upwards [h_ae1, h_ae2, h_lt_top, h_integrable.1, h_int.1]
    with a h_eq_one h_mul_eq h_lt_top h_int' h_int
  calc f (μ.rnDeriv ν a).toReal
    = f (μ.rnDeriv ν a * ∫⁻ b, (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) ∂(η a)).toReal := by simp [h_eq_one]
  _ = f (∫⁻ b, (μ.rnDeriv ν a) * (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) (a, b) ∂(η a)).toReal := by
    rw [lintegral_const_mul _ (by fun_prop)]
  _ = f (∫⁻ b, (μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b) ∂(η a)).toReal := by
    congr 2
    refine lintegral_congr_ae ?_
    filter_upwards [h_mul_eq] with b hb using hb
  _ = f (∫ b, ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b)).toReal ∂(η a)) := by
    rw [integral_toReal (by fun_prop) h_lt_top]
  _ ≤ ∫ b, f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (a, b)).toReal ∂(η a) := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp) h_int' h_int

lemma _root_.ConvexOn.integrable_apply_rnDeriv_of_integrable_compProd
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsMarkovKernel κ] [IsMarkovKernel η]
    (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont : ContinuousOn f (Ici 0))
    (hf_int : Integrable (fun p ↦ f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) p).toReal) (ν ⊗ₘ η))
    (hκη : μ ⊗ₘ κ ≪ μ ⊗ₘ η) :
    Integrable (fun a ↦ f (μ.rnDeriv ν a).toReal) ν := by
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le (convex_Ici 0)
  refine integrable_of_le_of_le (f := fun a ↦ f (μ.rnDeriv ν a).toReal)
    (g₁ := fun x ↦ c * (μ.rnDeriv ν x).toReal + c')
    (g₂ := fun x ↦ ∫ b, f ((μ ⊗ₘ κ).rnDeriv (ν ⊗ₘ η) (x, b)).toReal ∂(η x))
    ?_ ?_ ?_ (by fun_prop) ?_
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ fun x ↦ h _ ENNReal.toReal_nonneg
  · exact hf_cvx.apply_rnDeriv_ae_le_integral hf hf_cont hf_int hκη
  · exact hf_int.integral_compProd

end Integrable

end MeasureTheory
