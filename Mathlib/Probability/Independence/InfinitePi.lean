/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ProductMeasure

/-!
# Random variables are independent iff their joint distribution is the product measure.
-/

open MeasureTheory Measure ProbabilityTheory

namespace ProbabilityTheory

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒳 : ι → Type*} {m𝒳 : ∀ i, MeasurableSpace (𝒳 i)} (X : Π i, Ω → 𝒳 i)

/-- Random variables are independent iff their joint distribution is the product measure. -/
lemma iIndepFun_iff_map_fun_eq_infinitePi_map (mX : ∀ i, Measurable (X i)) :
    haveI := fun i ↦ isProbabilityMeasure_map (μ := μ) (mX i).aemeasurable
    iIndepFun X μ ↔ μ.map (fun ω i ↦ X i ω) = (infinitePi (fun i ↦ μ.map (X i))) where
  mp h := by
    haveI := fun i ↦ isProbabilityMeasure_map (μ := μ) (mX i).aemeasurable
    apply eq_infinitePi
    intro s t ht
    rw [iIndepFun_iff_finite] at h
    have : s.toSet.pi t = s.restrict ⁻¹' ((@Set.univ s ).pi fun i ↦ t i) := by ext; simp
    rw [this, ← map_apply, map_map]
    · have : s.restrict ∘ (fun ω i ↦ X i ω) = fun ω i ↦ s.restrict X i ω := by ext; simp
      rw [this, (iIndepFun_iff_map_fun_eq_pi_map ?_).1 (h s), pi_pi]
      · simp only [Finset.restrict]
        rw [s.prod_coe_sort fun i ↦ μ.map (X i) (t i)]
      exact fun i ↦ (mX i).aemeasurable
    any_goals fun_prop
    exact MeasurableSet.univ_pi fun i ↦ ht i i.2
  mpr h := by
    rw [iIndepFun_iff_finite]
    intro s
    rw [iIndepFun_iff_map_fun_eq_pi_map]
    · have : s.restrict ∘ (fun ω i ↦ X i ω) = fun ω i ↦ s.restrict X i ω := by ext; simp
      rw [← this, ← map_map, h, infinitePi_map_restrict]
      · simp
      all_goals fun_prop
    exact fun i ↦ (mX i).aemeasurable

/-- Random variables are independent iff their joint distribution is the product measure. This is
an `AEMeasurable` version of `iIndepFun_iff_map_fun_eq_infinitePi_map`, which is why it requires
`ι` to be countable. -/
lemma iIndepFun_iff_map_fun_eq_infinitePi_map₀ [Countable ι] (mX : ∀ i, AEMeasurable (X i) μ) :
    haveI _ i := isProbabilityMeasure_map (mX i)
    iIndepFun X μ ↔ μ.map (fun ω i ↦ X i ω) = (infinitePi (fun i ↦ μ.map (X i))) := by
  rw [iIndepFun_congr_iff (fun i ↦ (mX i).ae_eq_mk), iIndepFun_iff_map_fun_eq_infinitePi_map]
  · have : (fun ω i ↦ (mX i).mk (X i) ω) =ᵐ[μ] fun ω i ↦ X i ω := by
      change ∀ᵐ ω ∂μ, (fun i ↦ (mX i).mk (X i) ω) = fun i ↦ X i ω
      simp_rw [funext_iff]
      rw [MeasureTheory.ae_all_iff]
      exact fun i ↦ (mX i).ae_eq_mk.symm
    simp_rw [Measure.map_congr this, fun i ↦ Measure.map_congr (mX i).ae_eq_mk.symm]
  exact fun i ↦ (mX i).measurable_mk

end ProbabilityTheory
