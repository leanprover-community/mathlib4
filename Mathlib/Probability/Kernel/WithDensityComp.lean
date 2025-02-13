/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.WithDensity

/-!
# Results about the interaction of `Kernel.withDensity` and the composition and product of kernels

## Main statements

* `compProd_withDensity`: `μ ⊗ₘ (κ.withDensity f) = (μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2)`

-/

open ProbabilityTheory

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ : Kernel α β}
  {f : α → β → ℝ≥0∞}

lemma compProd_withDensity_apply_prod [SFinite μ] [IsSFiniteKernel κ]
    [IsSFiniteKernel (κ.withDensity f)] (hf : Measurable (Function.uncurry f))
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ ⊗ₘ (κ.withDensity f)) (s ×ˢ t)
      = ((μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2)) (s ×ˢ t) := by
  rw [Measure.compProd_apply (hs.prod ht), withDensity_apply _ (hs.prod ht),
    Measure.setLIntegral_compProd _ hs ht]
  swap; · exact hf
  have h_indicator a : ((κ.withDensity f) a) (Prod.mk a ⁻¹' s ×ˢ t)
      = s.indicator (fun a ↦ ∫⁻ b in t, f a b ∂(κ a)) a := by
    rw [Kernel.withDensity_apply _ hf, withDensity_apply]
    · by_cases has : a ∈ s <;> simp [has]
    · exact measurable_prod_mk_left (hs.prod ht)
  simp_rw [h_indicator]
  rw [lintegral_indicator hs]

lemma compProd_withDensity_of_isFiniteMeasure [IsFiniteMeasure μ] [IsSFiniteKernel κ]
    [IsFiniteKernel (κ.withDensity f)] (hf : Measurable (Function.uncurry f)) :
    μ ⊗ₘ (κ.withDensity f) = (μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2) := by
  ext s hs
  refine MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_ s hs
  · simp
  · rintro u ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_setOf_eq] at hs ht ⊢
    exact compProd_withDensity_apply_prod hf hs ht
  · intro t ht h
    rw [measure_compl ht, measure_compl ht, h]
    rotate_left
    · suffices IsFiniteMeasure ((μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2)) from measure_ne_top _ _
      constructor
      rw [← Set.univ_prod_univ, ← compProd_withDensity_apply_prod hf .univ .univ]
      exact measure_lt_top _ _
    · exact measure_ne_top _ _
    congr 1
    rw [← Set.univ_prod_univ, compProd_withDensity_apply_prod hf .univ .univ]
  · intro f h_disj hf h
    simp_rw [measure_iUnion h_disj hf, h]

lemma compProd_withDensity [SFinite μ] [IsSFiniteKernel κ] [IsFiniteKernel (κ.withDensity f)]
    (hf : Measurable (Function.uncurry f)) :
    μ ⊗ₘ (κ.withDensity f) = (μ ⊗ₘ κ).withDensity (fun p ↦ f p.1 p.2) := by
  rw [← sum_sfiniteSeq μ, compProd_sum_left, compProd_sum_left, withDensity_sum]
  congr with n : 1
  exact compProd_withDensity_of_isFiniteMeasure hf

end MeasureTheory.Measure
