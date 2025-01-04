/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Composition.ParallelComp
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Composition of a measure and a kernel

This operation, denoted by `∘ₘ`, takes `μ : Measure α` and `κ : Kernel α β` and creates
`κ ∘ₘ μ : Measure β`. The integral of a function against `κ ∘ₘ μ` is
`∫⁻ x, f x ∂(κ ∘ₘ μ) = ∫⁻ a, ∫⁻ b, f b ∂(κ a) ∂μ`.

This file does not define composition but only introduces notation for
`MeasureTheory.Measure.bind μ κ`.

## Notations

* `κ ∘ₘ μ = MeasureTheory.Measure.bind μ κ`
-/

open scoped ENNReal

open ProbabilityTheory  MeasureTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β}

/-- Composition of a measure and a kernel.

Defined using `MeasureTheory.Measure.bind` -/
scoped[ProbabilityTheory] notation3 κ " ∘ₘ " μ:100 => MeasureTheory.Measure.bind μ κ

lemma map_comp (μ : Measure α) (κ : Kernel α β) {f : β → γ} (hf : Measurable f) :
    (κ ∘ₘ μ).map f = (κ.map f) ∘ₘ μ := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.bind_apply (hf hs) κ.measurable,
    Measure.bind_apply hs (Kernel.measurable _)]
  simp_rw [Kernel.map_apply' _ hf _ hs]

lemma comp_assoc {η : Kernel β γ} : η ∘ₘ (κ ∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ :=
  Measure.bind_bind κ.measurable η.measurable

lemma comp_deterministic_eq_map {f : α → β} (hf : Measurable f) :
    Kernel.deterministic f hf ∘ₘ μ = μ.map f :=
  Measure.bind_dirac_eq_map μ hf

@[simp]
lemma comp_id : Kernel.id ∘ₘ μ = μ := by rw [Kernel.id, comp_deterministic_eq_map, Measure.map_id]

@[simp]
lemma snd_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).snd = κ ∘ₘ μ := by
  ext s hs
  rw [bind_apply hs κ.measurable, snd_apply hs, compProd_apply]
  · rfl
  · exact measurable_snd hs

lemma comp_swap {μ : Measure (α × β)} : (Kernel.swap α β) ∘ₘ μ = μ.map Prod.swap :=
  comp_deterministic_eq_map measurable_swap

lemma compProd_eq_comp_prod (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    μ ⊗ₘ κ = (Kernel.id ×ₖ κ) ∘ₘ μ := by
  rw [compProd, Kernel.compProd_prodMkLeft_eq_comp]
  rfl

lemma compProd_eq_parallelComp_comp_copy_comp (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] :
    μ ⊗ₘ κ = (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy α ∘ₘ μ := by
  rw [compProd_eq_comp_prod, ← Kernel.parallelComp_comp_copy, Measure.comp_assoc]

lemma compProd_id [SFinite μ] : μ ⊗ₘ Kernel.id = μ.map (fun x ↦ (x, x)) := by
  rw [compProd_eq_comp_prod, Kernel.id, Kernel.deterministic_prod_deterministic,
    comp_deterministic_eq_map]
  rfl

lemma compProd_id_eq_copy_comp [SFinite μ] : μ ⊗ₘ Kernel.id = Kernel.copy α ∘ₘ μ := by
  rw [compProd_id, Kernel.copy, comp_deterministic_eq_map]

@[simp]
lemma comp_const {ν : Measure β} : (Kernel.const α ν) ∘ₘ μ = μ .univ • ν := μ.bind_const

instance [SFinite μ] [IsSFiniteKernel κ] : SFinite (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance

instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance

instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance

@[simp]
lemma comp_apply_univ [IsMarkovKernel κ] : (κ ∘ₘ μ) .univ = μ .univ := by
  rw [bind_apply .univ κ.measurable]
  simp

@[simp]
lemma comp_add_right [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] :
    κ ∘ₘ (μ + ν) = κ ∘ₘ μ + κ ∘ₘ ν := by
  simp_rw [← snd_compProd, compProd_add_left]
  simp

lemma comp_add_left [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (κ + η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ := by
  simp_rw [← snd_compProd, compProd_add_right]
  simp

/-- Same as `comp_add_left` except that it uses `⇑κ + ⇑η` instead of `⇑(κ + η)` in order to have
a simp-normal form on the left of the equality. -/
@[simp]
lemma comp_add_left' [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (⇑κ + ⇑η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ := by rw [← Kernel.coe_add, comp_add_left]

lemma comp_smul_left (a : ℝ≥0∞) : κ ∘ₘ (a • μ) = a • (κ ∘ₘ μ) := by
  ext s hs
  simp only [bind_apply hs κ.measurable, lintegral_smul_measure, smul_apply, smul_eq_mul]

section AbsolutelyContinuous

lemma AbsolutelyContinuous.comp [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ ν := by
  simp_rw [← snd_compProd, Measure.snd]
  exact (hμν.compProd hκη).map measurable_snd

lemma AbsolutelyContinuous.comp_right [SFinite μ] [SFinite ν]
    (hμν : μ ≪ ν) (κ : Kernel α γ) [IsSFiniteKernel κ]  :
    κ ∘ₘ μ ≪ κ ∘ₘ ν :=
  hμν.comp (ae_of_all μ fun _ _ a ↦ a)

lemma AbsolutelyContinuous.comp_left (μ : Measure α) [SFinite μ]
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ μ :=
  μ.absolutelyContinuous_refl.comp hκη

end AbsolutelyContinuous

end MeasureTheory.Measure

section ParallelComp

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
  {μ ν : Measure α} {κ η : Kernel α β}

lemma MeasureTheory.Measure.prod_comp_right
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (κ : Kernel β γ) [IsSFiniteKernel κ] :
    μ.prod (κ ∘ₘ ν) = (Kernel.id ∥ₖ κ) ∘ₘ (μ.prod ν) := by
  ext s hs
  rw [Measure.prod_apply hs, Measure.bind_apply hs (Kernel.measurable _)]
  simp_rw [Measure.bind_apply (measurable_prod_mk_left hs) (Kernel.measurable _)]
  rw [MeasureTheory.lintegral_prod]
  swap; · exact (Kernel.measurable_coe _ hs).aemeasurable
  congr with a
  congr with b
  rw [Kernel.parallelComp_apply, Kernel.id_apply, Measure.prod_apply hs, lintegral_dirac']
  exact measurable_measure_prod_mk_left hs

lemma MeasureTheory.Measure.prod_comp_left
    (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν]
    (κ : Kernel α γ) [IsSFiniteKernel κ] :
    (κ ∘ₘ μ).prod ν = (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) := by
  have h1 : (κ ∘ₘ μ).prod ν = (ν.prod (κ ∘ₘ μ)).map Prod.swap := by
    rw [Measure.prod_swap]
  have h2 : (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν) = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
    calc (κ ∥ₖ Kernel.id) ∘ₘ (μ.prod ν)
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((ν.prod μ).map Prod.swap) := by rw [Measure.prod_swap]
    _ = (κ ∥ₖ Kernel.id) ∘ₘ ((Kernel.swap _ _) ∘ₘ (ν.prod μ)) := by
      rw [Kernel.swap, Measure.comp_deterministic_eq_map]
    _ = (Kernel.swap _ _) ∘ₘ ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)) := by
      rw [Measure.comp_assoc, Measure.comp_assoc, Kernel.swap_parallelComp]
    _ = ((Kernel.id ∥ₖ κ) ∘ₘ (ν.prod μ)).map Prod.swap := by
      rw [Kernel.swap, Measure.comp_deterministic_eq_map]
  rw [← Measure.prod_comp_right, ← h1] at h2
  exact h2.symm

namespace ProbabilityTheory.Kernel

variable {α' β' γ' : Type*} {mα' : MeasurableSpace α'} {mβ' : MeasurableSpace β'}
  {mγ' : MeasurableSpace γ'}

lemma parallelComp_comp_right (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α' γ) [IsSFiniteKernel η] (ξ : Kernel γ δ) [IsSFiniteKernel ξ] :
    κ ∥ₖ (ξ ∘ₖ η) = (Kernel.id ∥ₖ ξ) ∘ₖ (κ ∥ₖ η) := by
  ext a
  rw [parallelComp_apply, comp_apply, comp_apply, parallelComp_apply, Measure.prod_comp_right]

lemma parallelComp_comp_left (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α' γ) [IsSFiniteKernel η] (ξ : Kernel γ δ) [IsSFiniteKernel ξ] :
    (ξ ∘ₖ η) ∥ₖ κ = (ξ ∥ₖ Kernel.id) ∘ₖ (η ∥ₖ κ) := by
  ext a
  rw [parallelComp_apply, comp_apply, comp_apply, parallelComp_apply, Measure.prod_comp_left]

lemma parallelComp_comm (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel γ δ) [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ κ) ∘ₖ (η ∥ₖ Kernel.id) = (η ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ κ) := by
  rw [← parallelComp_comp_right, ← parallelComp_comp_left, comp_id, comp_id]

lemma parallelComp_comp_parallelComp
    {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFiniteKernel η]
    {κ' : Kernel α' β'} [IsSFiniteKernel κ'] {η' : Kernel β' γ'} [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ∥ₖ κ') = (η ∘ₖ κ) ∥ₖ (η' ∘ₖ κ') := by
  rw [parallelComp_comp_right, parallelComp_comp_left, ← comp_assoc, ← parallelComp_comp_right,
    comp_id]

lemma parallelComp_comp_prod
    {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFiniteKernel η]
    {κ' : Kernel α β'} [IsSFiniteKernel κ'] {η' : Kernel β' γ'} [IsSFiniteKernel η'] :
    (η ∥ₖ η') ∘ₖ (κ ×ₖ κ') = (η ∘ₖ κ) ×ₖ (η' ∘ₖ κ') := by
  rw [← parallelComp_comp_copy, ← comp_assoc, parallelComp_comp_parallelComp,
    ← parallelComp_comp_copy]

lemma parallelComp_comp_id_left_right (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ η) ∘ₖ (κ ∥ₖ Kernel.id) = κ ∥ₖ η := by
  rw [← parallelComp_comp_right, comp_id]

lemma parallelComp_comp_id_right_left (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel γ δ) [IsSFiniteKernel η] :
    (κ ∥ₖ Kernel.id) ∘ₖ (Kernel.id ∥ₖ η) = κ ∥ₖ η := by
  rw [← parallelComp_comp_left, comp_id]

end ProbabilityTheory.Kernel

lemma MeasureTheory.Measure.parallelComp_comp_compProd [SFinite μ]
    {κ : Kernel α β} [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ η) ∘ₘ (μ ⊗ₘ κ) = μ ⊗ₘ (η ∘ₖ κ) := by
  rw [Measure.compProd_eq_comp_prod, Measure.compProd_eq_comp_prod, Measure.comp_assoc,
    Kernel.parallelComp_comp_prod, Kernel.id_comp]

end ParallelComp
