/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.ParallelComp

/-!
# Composition of a measure and a kernel

This operation, denoted by `⊗ₘ`, takes `μ : Measure α` and `κ : Kernel α β` and creates
`μ ⊗ₘ κ : Measure (α × β)`. The integral of a function against `μ ⊗ₘ κ` is
`∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ`.

`μ ⊗ₘ κ` is defined as `((Kernel.const Unit μ) ⊗ₖ (Kernel.prodMkLeft Unit κ)) ()`.

## Main definitions

* `Measure.compProd`: from `μ : Measure α` and `κ : Kernel α β`, get a `Measure (α × β)`.

## Notations

* `μ ⊗ₘ κ = μ.compProd κ`
-/

open scoped ENNReal

open ProbabilityTheory

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

lemma comp_assoc {μ : Measure α} {κ : Kernel α β} {η : Kernel β γ} :
    η ∘ₘ (κ ∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ :=
  Measure.bind_bind κ.measurable η.measurable

lemma comp_deterministic_eq_map {f : α → β} (hf : Measurable f) :
    Kernel.deterministic f hf ∘ₘ μ = μ.map f :=
  Measure.bind_dirac_eq_map μ hf

@[simp]
lemma comp_id : Kernel.id ∘ₘ μ = μ := by
  rw [Kernel.id, Measure.comp_deterministic_eq_map, Measure.map_id]

lemma comp_eq_snd_compProd (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ] :
    κ ∘ₘ μ = (μ ⊗ₘ κ).snd := by
  ext s hs
  rw [Measure.bind_apply hs κ.measurable, Measure.snd_apply hs, Measure.compProd_apply]
  · rfl
  · exact measurable_snd hs

lemma fst_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).fst = μ := by
  ext s
  rw [Measure.compProd, Measure.fst, ← Kernel.fst_apply, Kernel.fst_compProd, Kernel.const_apply]

lemma snd_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).snd = κ ∘ₘ μ := (Measure.comp_eq_snd_compProd μ κ).symm

lemma compProd_eq_comp (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    μ ⊗ₘ κ = (Kernel.id ×ₖ κ) ∘ₘ μ := by
  rw [Measure.compProd, Kernel.compProd_prodMkLeft_eq_comp]
  rfl

lemma compProd_id [SFinite μ] : μ ⊗ₘ Kernel.id = μ.map (fun x ↦ (x, x)) := by
  rw [Measure.compProd_eq_comp, Kernel.id, Kernel.deterministic_prod_deterministic,
    Measure.comp_deterministic_eq_map]
  rfl

/-- The composition product of a measure and a constant kernel is the product between the two
measures. -/
@[simp]
lemma compProd_const {ν : Measure β} [SFinite μ] [SFinite ν] :
    μ ⊗ₘ (Kernel.const α ν) = μ.prod ν := by
  ext s hs
  rw [Measure.compProd_apply hs, Measure.prod_apply hs]
  simp_rw [Kernel.const_apply]

@[simp]
lemma comp_const {ν : Measure β} : (Kernel.const α ν) ∘ₘ μ = μ .univ • ν := μ.bind_const

lemma compProd_apply_toReal [SFinite μ] [IsFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    ((μ ⊗ₘ κ) s).toReal = ∫ x, (κ x (Prod.mk x ⁻¹' s)).toReal ∂μ := by
  rw [Measure.compProd_apply hs, integral_eq_lintegral_of_nonneg_ae]
  rotate_left
  · exact ae_of_all _ (fun x ↦ by positivity)
  · exact (Kernel.measurable_kernel_prod_mk_left hs).ennreal_toReal.aestronglyMeasurable
  congr with x
  rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma compProd_univ_toReal [SFinite μ] [IsFiniteKernel κ] :
    ((μ ⊗ₘ κ) .univ).toReal = ∫ x, (κ x .univ).toReal ∂μ :=
  compProd_apply_toReal .univ

lemma fst_sum {ι : Type*} (μ : ι → Measure (α × β)) :
    (Measure.sum μ).fst = Measure.sum (fun n ↦ (μ n).fst) := by
  ext s hs
  rw [Measure.fst_apply hs, Measure.sum_apply, Measure.sum_apply _ hs]
  · congr with i
    rw [Measure.fst_apply hs]
  · exact measurable_fst hs

lemma snd_sum {ι : Type*} (μ : ι → Measure (α × β)) :
    (Measure.sum μ).snd = Measure.sum (fun n ↦ (μ n).snd) := by
  ext s hs
  rw [Measure.snd_apply hs, Measure.sum_apply, Measure.sum_apply _ hs]
  · congr with i
    rw [Measure.snd_apply hs]
  · exact measurable_snd hs

instance {μ : Measure (α × β)} [SFinite μ] : SFinite μ.fst :=
  ⟨fun n ↦ (sfiniteSeq μ n).fst, inferInstance, by rw [← Measure.fst_sum, sum_sfiniteSeq μ]⟩

instance {μ : Measure (α × β)} [SFinite μ] : SFinite μ.snd :=
  ⟨fun n ↦ (sfiniteSeq μ n).snd, inferInstance, by rw [← Measure.snd_sum, sum_sfiniteSeq μ]⟩

instance {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ] : SFinite (κ ∘ₘ μ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

instance {μ : Measure α} [IsFiniteMeasure μ] {κ : Kernel α β} [IsFiniteKernel κ] :
    IsFiniteMeasure (κ ∘ₘ μ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

instance {μ : Measure α} [IsProbabilityMeasure μ] {κ : Kernel α β} [IsMarkovKernel κ] :
    IsProbabilityMeasure (κ ∘ₘ μ) := by
  rw [Measure.comp_eq_snd_compProd]
  infer_instance

lemma fst_swap_compProd [SFinite μ] [IsSFiniteKernel κ] :
    ((μ ⊗ₘ κ).map Prod.swap).fst = κ ∘ₘ μ := by
  simp [Measure.comp_eq_snd_compProd]

lemma compProd_apply_univ [SFinite μ] [IsMarkovKernel κ] :
    (μ ⊗ₘ κ) .univ = μ .univ := by
  rw [Measure.compProd_apply .univ]
  simp

lemma comp_apply_univ [IsMarkovKernel κ] : (κ ∘ₘ μ) .univ = μ .univ := by
  rw [Measure.bind_apply .univ κ.measurable]
  simp

@[simp]
lemma fst_add {μ ν : Measure (α × β)} : (μ + ν).fst = μ.fst + ν.fst := by
  ext s hs
  simp_rw [Measure.coe_add, Pi.add_apply, Measure.fst_apply hs, Measure.coe_add, Pi.add_apply]

@[simp]
lemma snd_add {μ ν : Measure (α × β)} : (μ + ν).snd = μ.snd + ν.snd := by
  ext s hs
  simp_rw [Measure.coe_add, Pi.add_apply, Measure.snd_apply hs, Measure.coe_add, Pi.add_apply]

lemma comp_add_right [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] :
    κ ∘ₘ (μ + ν) = κ ∘ₘ μ + κ ∘ₘ ν := by
  simp_rw [comp_eq_snd_compProd]
  rw [Measure.compProd_add_left]
  simp

lemma comp_add_left [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (κ + η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ := by
  simp_rw [comp_eq_snd_compProd]
  rw [Measure.compProd_add_right]
  simp

lemma compProd_smul_left (a : ℝ≥0∞) [SFinite μ] [IsSFiniteKernel κ] :
    (a • μ) ⊗ₘ κ = a • (μ ⊗ₘ κ) := by
  ext s hs
  simp only [Measure.compProd_apply hs, lintegral_smul_measure, Measure.smul_apply, smul_eq_mul]

lemma comp_smul_left (a : ℝ≥0∞) : κ ∘ₘ (a • μ) = a • (κ ∘ₘ μ) := by
  ext s hs
  simp only [Measure.bind_apply hs κ.measurable, lintegral_smul_measure, Measure.smul_apply,
    smul_eq_mul]

section AbsolutelyContinuous

lemma absolutelyContinuous_comp [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ ν := by
  simp_rw [Measure.comp_eq_snd_compProd, Measure.snd]
  exact Measure.AbsolutelyContinuous.map (Measure.absolutelyContinuous_compProd hμν hκη)
    measurable_snd

lemma absolutelyContinuous_comp_left [SFinite μ] [SFinite ν]
    (hμν : μ ≪ ν) (κ : Kernel α γ) [IsSFiniteKernel κ]  :
    κ ∘ₘ μ ≪ κ ∘ₘ ν :=
  absolutelyContinuous_comp hμν (ae_of_all μ fun _ _ a ↦ a)

lemma absolutelyContinuous_comp_right (μ : Measure α) [SFinite μ]
    [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ μ :=
  Measure.absolutelyContinuous_comp μ.absolutelyContinuous_refl hκη

end AbsolutelyContinuous

end MeasureTheory.Measure
