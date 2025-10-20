/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Lemmas relating different ways to compose kernels

This file contains lemmas about the composition of kernels that involve several types of
compositions/products.

## Main statements

* `comp_eq_snd_compProd`: `η ∘ₖ κ = snd (κ ⊗ₖ prodMkLeft X η)`
* `parallelComp_comp_parallelComp`: `(η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ')`
* `deterministic_comp_copy`: for a deterministic kernel, copying then applying the kernel to
  the two copies is the same as first applying the kernel then copying. That is, if `κ` is
  a deterministic kernel, `(κ ∥ₖ κ) ∘ₖ copy X = copy Y ∘ₖ κ`.

-/


open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {X Y Z T : Type*} {mX : MeasurableSpace X} {mY : MeasurableSpace Y}
  {mZ : MeasurableSpace Z} {mT : MeasurableSpace T}
  {μ : Measure X} {ν : Measure Y} {κ : Kernel X Y} {η : Kernel Z T}

namespace ProbabilityTheory.Kernel

theorem comp_eq_snd_compProd (η : Kernel Y Z) [IsSFiniteKernel η] (κ : Kernel X Y)
    [IsSFiniteKernel κ] : η ∘ₖ κ = snd (κ ⊗ₖ prodMkLeft X η) := by
  ext a s hs
  rw [comp_apply' _ _ _ hs, snd_apply' _ _ hs, compProd_apply (measurable_snd hs)]
  simp [← Set.preimage_comp]

@[simp] lemma snd_compProd_prodMkLeft
    (κ : Kernel X Y) (η : Kernel Y Z) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    snd (κ ⊗ₖ prodMkLeft X η) = η ∘ₖ κ := (comp_eq_snd_compProd η κ).symm

lemma compProd_prodMkLeft_eq_comp
    (κ : Kernel X Y) [IsSFiniteKernel κ] (η : Kernel Y Z) [IsSFiniteKernel η] :
    κ ⊗ₖ (prodMkLeft X η) = (Kernel.id ×ₖ η) ∘ₖ κ := by
  ext a s hs
  rw [comp_eq_snd_compProd, compProd_apply hs, snd_apply' _ _ hs, compProd_apply]
  swap; · exact measurable_snd hs
  simp only [prodMkLeft_apply, ← Set.preimage_comp, Prod.snd_comp_mk, Set.preimage_id_eq, id_eq,
    prod_apply' _ _ _ hs, id_apply]
  congr with b
  rw [lintegral_dirac']
  exact measurable_measure_prodMk_left hs

lemma swap_parallelComp : swap Y T ∘ₖ (κ ∥ₖ η) = η ∥ₖ κ ∘ₖ swap X Z := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  ext ac s hs
  simp_rw [comp_apply, parallelComp_apply, Measure.bind_apply hs (Kernel.aemeasurable _),
    swap_apply, lintegral_dirac' _ (Kernel.measurable_coe _ hs), parallelComp_apply' hs,
    Prod.fst_swap, Prod.snd_swap]
  rw [MeasureTheory.lintegral_prod_symm]
  swap; · exact ((Kernel.id.measurable_coe hs).comp measurable_swap).aemeasurable
  congr with d
  simp_rw [Prod.swap_prod_mk, Measure.dirac_apply' _ hs, ← Set.indicator_comp_right,
    lintegral_indicator (measurable_prodMk_left hs)]
  simp

/-- For a deterministic kernel, copying then applying the kernel to the two copies is the same
as first applying the kernel then copying. -/
lemma deterministic_comp_copy {f : X → Y} (hf : Measurable f) :
    (deterministic f hf ∥ₖ deterministic f hf) ∘ₖ copy X = copy Y ∘ₖ deterministic f hf := by
  simp_rw [parallelComp_comp_copy, deterministic_prod_deterministic, copy,
    deterministic_comp_deterministic, Function.comp_def]

section ParallelComp

variable {X' Y' Z' : Type*} {mX' : MeasurableSpace X'} {mY' : MeasurableSpace Y'}
  {mZ' : MeasurableSpace Z'}

lemma parallelComp_id_left_comp_parallelComp
    {η : Kernel X' Z} [IsSFiniteKernel η] {ξ : Kernel Z T} [IsSFiniteKernel ξ] :
    (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) = κ ∥ₖ (ξ ∘ₖ η) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  ext a s hs
  rw [comp_apply' _ _ _ hs, parallelComp_apply,
    MeasureTheory.lintegral_prod _ (Kernel.measurable_coe _ hs).aemeasurable]
  rw [parallelComp_apply, Measure.prod_apply hs]
  congr with x
  rw [comp_apply' _ _ _ (measurable_prodMk_left hs)]
  congr with y
  rw [parallelComp_apply' hs, Kernel.id_apply,
    lintegral_dirac' _ (measurable_measure_prodMk_left hs)]

lemma parallelComp_id_right_comp_parallelComp {η : Kernel X' Z} [IsSFiniteKernel η]
    {ξ : Kernel Z T} [IsSFiniteKernel ξ] :
    (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = (ξ ∘ₖ η) ∥ₖ κ := by
  suffices swap T Y ∘ₖ (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) = swap T Y ∘ₖ ((ξ ∘ₖ η) ∥ₖ κ) by
    calc ξ ∥ₖ Kernel.id ∘ₖ (η ∥ₖ κ)
    _ = swap Y T ∘ₖ (swap T Y ∘ₖ (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ)) := by
      simp_rw [← comp_assoc, swap_swap, id_comp]
    _ = swap Y T ∘ₖ (swap T Y ∘ₖ ((ξ ∘ₖ η) ∥ₖ κ)) := by rw [this]
    _ = ξ ∘ₖ η ∥ₖ κ := by simp_rw [← comp_assoc, swap_swap, id_comp]
  simp_rw [swap_parallelComp, comp_assoc, swap_parallelComp, ← comp_assoc,
    parallelComp_id_left_comp_parallelComp]

lemma parallelComp_comp_parallelComp [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η]
    {κ' : Kernel X' Y'} [IsSFiniteKernel κ'] {η' : Kernel Y' Z'} [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by
  rw [← parallelComp_id_left_comp_parallelComp, ← parallelComp_id_right_comp_parallelComp,
    ← comp_assoc, parallelComp_id_left_comp_parallelComp, comp_id]

lemma parallelComp_comp_prod [IsSFiniteKernel κ] {η : Kernel Y Z} [IsSFiniteKernel η]
    {κ' : Kernel X Y'} [IsSFiniteKernel κ'] {η' : Kernel Y' Z'} [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  rw [← parallelComp_comp_copy, ← comp_assoc, parallelComp_comp_parallelComp,
    ← parallelComp_comp_copy]

lemma parallelComp_comm {η : Kernel Z T} :
    (Kernel.id ∥ₖ κ) ∘ₖ (η ∥ₖ Kernel.id) = (η ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ κ) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  by_cases hη : IsSFiniteKernel η
  swap; · simp [hη]
  rw [parallelComp_id_left_comp_parallelComp, parallelComp_id_right_comp_parallelComp,
    comp_id, comp_id]

end ParallelComp

end ProbabilityTheory.Kernel
