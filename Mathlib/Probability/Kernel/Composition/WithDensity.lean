/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.CompNotation
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.WithDensity

import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Composition of kernels and measures with density

We prove lemmas about `Kernel.withDensity` and `Measure.withDensity` in relation with the
composition of kernels and measures.

-/

public section

open ProbabilityTheory MeasureTheory
open scoped ENNReal

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {κ : Kernel α β} [IsSFiniteKernel κ]
  {f : α → ℝ≥0∞} {f' : β → ℝ≥0∞} {g : α → β → ℝ≥0∞}

namespace MeasureTheory.Measure

lemma withDensity_comp (hf' : Measurable f') :
    (κ ∘ₘ μ).withDensity f' = (κ.withDensity (fun _ b ↦ f' b)) ∘ₘ μ := by
  refine Measure.ext_of_lintegral _ fun g hg ↦ Eq.symm ?_
  calc ∫⁻ b, g b ∂((κ.withDensity (fun _ b ↦ f' b)) ∘ₘ μ)
      = ∫⁻ a, ∫⁻ b, g b ∂(κ.withDensity (fun _ b ↦ f' b)) a ∂μ :=
        Measure.lintegral_bind (Kernel.measurable _).aemeasurable hg.aemeasurable
    _ = ∫⁻ a, ∫⁻ b, f' b * g b ∂κ a ∂μ := by
        congr with a
        exact Kernel.lintegral_withDensity _ (by fun_prop) _ hg
    _ = ∫⁻ b, f' b * g b ∂(κ ∘ₘ μ) :=
        (Measure.lintegral_bind (Kernel.measurable _).aemeasurable (hf'.mul hg).aemeasurable).symm
    _ = ∫⁻ b, g b ∂((κ ∘ₘ μ).withDensity f') :=
        (lintegral_withDensity_eq_lintegral_mul _ hf' hg).symm

/-- A composition-product of a measure with a kernel defined with `withDensity` is equal to the
`withDensity` of the composition-product. -/
lemma compProd_withDensity [SFinite μ]
    [IsSFiniteKernel (κ.withDensity g)] (hf : Measurable (Function.uncurry g)) :
    μ ⊗ₘ (κ.withDensity g) = (μ ⊗ₘ κ).withDensity (fun p ↦ g p.1 p.2) := by
  ext s hs
  rw [compProd_apply hs, withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_compProd]
  · congr with a
    rw [Kernel.withDensity_apply' _ hf, ← lintegral_indicator (measurable_prodMk_left hs)]
    rfl
  · exact hf.indicator hs

lemma withDensity_compProd [SFinite μ] (hf : Measurable f) :
    (μ.withDensity f) ⊗ₘ κ = (μ ⊗ₘ κ).withDensity (fun ab ↦ f ab.1) := by
  refine ext_of_lintegral _ fun g hg ↦ ?_
  calc ∫⁻ ab, g ab ∂((μ.withDensity f) ⊗ₘ κ)
  _ = ∫⁻ a, ∫⁻ b, g (a, b) ∂κ a ∂(μ.withDensity f) := lintegral_compProd hg
  _ = ∫⁻ a, f a * ∫⁻ b, g (a, b) ∂κ a ∂μ :=
      lintegral_withDensity_eq_lintegral_mul _ hf hg.lintegral_kernel_prod_right'
  _ = ∫⁻ a, ∫⁻ b, f a * g (a, b) ∂κ a ∂μ :=
      lintegral_congr fun a ↦ (lintegral_const_mul _ (by fun_prop)).symm
  _ = ∫⁻ ab, (fun ab ↦ f ab.1) ab * g ab ∂(μ ⊗ₘ κ) :=
      (lintegral_compProd ((hf.comp measurable_fst).mul hg)).symm
  _ = ∫⁻ ab, g ab ∂((μ ⊗ₘ κ).withDensity (fun ab ↦ f ab.1)) :=
      (lintegral_withDensity_eq_lintegral_mul _ (hf.comp measurable_fst) hg).symm

lemma withDensity_compProd_withDensity [SFinite μ]
    (hf : Measurable f) (hg : Measurable (Function.uncurry g)) [IsSFiniteKernel (κ.withDensity g)] :
    (μ.withDensity f) ⊗ₘ (κ.withDensity g) =
      (μ ⊗ₘ κ).withDensity (fun ac ↦ f ac.1 * g ac.1 ac.2) := by
  rw [compProd_withDensity hg, withDensity_compProd hf]
  exact (withDensity_mul _ (hf.comp measurable_fst) hg).symm

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

lemma withDensity_comp {η : Kernel β γ} [IsSFiniteKernel η] {f : α → ℝ≥0∞} (hf : Measurable f) :
    (η ∘ₖ κ).withDensity (fun a _ ↦ f a) = η ∘ₖ (κ.withDensity (fun a _ ↦ f a)) := by
  ext a s hs
  rw [Kernel.withDensity_apply _ (by fun_prop), Kernel.comp_apply, Kernel.comp_apply]
  conv_rhs => rw [Measure.bind_apply hs (by fun_prop)]
  simp only [withDensity_const, Measure.smul_apply, smul_eq_mul]
  rw [lintegral_withDensity _ (by fun_prop) _ (η.measurable_coe hs),
    Measure.bind_apply hs (Kernel.aemeasurable _), lintegral_const_mul _ (η.measurable_coe hs)]

lemma compProd_withDensity_left {η : Kernel (α × β) γ} [IsSFiniteKernel η]
    [IsSFiniteKernel (κ.withDensity g)] (hf : Measurable (Function.uncurry g)) :
    (κ.withDensity g) ⊗ₖ η = (κ ⊗ₖ η).withDensity (fun a bc ↦ g a bc.1) := by
  ext a : 1
  calc ((κ.withDensity g) ⊗ₖ η) a
  _ = (κ a).withDensity (g a) ⊗ₘ η.sectR a := by
      rw [compProd_apply_eq_compProd_sectR, Kernel.withDensity_apply _ hf]
  _ = ((κ a) ⊗ₘ (η.sectR a)).withDensity (fun bc ↦ g a bc.1) :=
      Measure.withDensity_compProd (by fun_prop)
  _ = ((κ ⊗ₖ η).withDensity (fun a bc ↦ g a bc.1)) a := by
      rw [← compProd_apply_eq_compProd_sectR, Kernel.withDensity_apply _ (by fun_prop)]

end ProbabilityTheory.Kernel
