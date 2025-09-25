/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Lemmas relating different ways to compose measures and kernels

This file contains lemmas about the composition of measures and kernels that do not fit in any of
the other files in this directory, because they involve several types of compositions/products.

-/

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
  {μ : Measure α} {ν : Measure β} {κ : Kernel α β}

namespace MeasureTheory.Measure

lemma compProd_eq_parallelComp_comp_copy_comp [SFinite μ] :
    μ ⊗ₘ κ = (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy α ∘ₘ μ := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  rw [compProd_eq_comp_prod, ← Kernel.parallelComp_comp_copy, Measure.comp_assoc]

lemma prod_comp_right [SFinite ν] {κ : Kernel β γ} [IsSFiniteKernel κ] :
    μ.prod (κ ∘ₘ ν) = (Kernel.id ∥ₖ κ) ∘ₘ (μ.prod ν) := by
  ext s hs
  rw [Measure.prod_apply hs, Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Measure.bind_apply (measurable_prodMk_left hs) (Kernel.aemeasurable _)]
  rw [MeasureTheory.lintegral_prod]
  swap; · exact (Kernel.measurable_coe _ hs).aemeasurable
  congr with a
  congr with b
  rw [Kernel.parallelComp_apply, Kernel.id_apply, Measure.prod_apply hs, lintegral_dirac']
  exact measurable_measure_prodMk_left hs

lemma prod_comp_left [SFinite μ] [SFinite ν] {κ : Kernel α γ} [IsSFiniteKernel κ] :
    (κ ∘ₘ μ).prod ν = (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) := by
  have h1 : (κ ∘ₘ μ).prod ν = (ν.prod (κ ∘ₘ μ)).map Prod.swap := by rw [Measure.prod_swap]
  have h2 : (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
    calc (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν)
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((ν.prod μ).map Prod.swap) := by rw [Measure.prod_swap]
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((Kernel.swap _ _) ∘ₘ (ν.prod μ)) := by
      rw [Kernel.swap, Measure.deterministic_comp_eq_map]
    _ = (Kernel.swap _ _) ∘ₘ ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)) := by
      rw [Measure.comp_assoc, Measure.comp_assoc, Kernel.swap_parallelComp]
    _ = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
      rw [Kernel.swap, Measure.deterministic_comp_eq_map]
  rw [← Measure.prod_comp_right, ← h1] at h2
  exact h2.symm

end MeasureTheory.Measure

lemma MeasureTheory.Measure.parallelComp_comp_compProd
    [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ η) ∘ₘ (μ ⊗ₘ κ) = μ ⊗ₘ (η ∘ₖ κ) := by
  by_cases hμ : SFinite μ
  swap; · simp [hμ]
  rw [Measure.compProd_eq_comp_prod, Measure.compProd_eq_comp_prod, Measure.comp_assoc,
    Kernel.parallelComp_comp_prod, Kernel.id_comp]
