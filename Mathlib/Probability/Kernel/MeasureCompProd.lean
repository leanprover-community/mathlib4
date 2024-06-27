/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.IntegralCompProd

/-!
# Composition-Product of a measure and a kernel

This operation, denoted by `⊗ₘ`, takes `μ : Measure α` and `κ : kernel α β` and creates
`μ ⊗ₘ κ : Measure (α × β)`. The integral of a function against `μ ⊗ₘ κ` is
`∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ`.

`μ ⊗ₘ κ` is defined as `((kernel.const Unit μ) ⊗ₖ (kernel.prodMkLeft Unit κ)) ()`.

## Main definitions

* `Measure.compProd`: from `μ : Measure α` and `κ : kernel α β`, get a `Measure (α × β)`.

## Notations

* `μ ⊗ₘ κ = μ.compProd κ`
-/

open scoped ENNReal

open ProbabilityTheory

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ : Measure α} {κ η : kernel α β}

/-- The composition-product of a measure and a kernel. -/
noncomputable
def compProd (μ : Measure α) (κ : kernel α β) : Measure (α × β) :=
  (kernel.const Unit μ ⊗ₖ kernel.prodMkLeft Unit κ) ()

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ⊗ₘ " => MeasureTheory.Measure.compProd

@[simp] lemma compProd_zero_left (κ : kernel α β) : (0 : Measure α) ⊗ₘ κ = 0 := by simp [compProd]
@[simp] lemma compProd_zero_right (μ : Measure α) : μ ⊗ₘ (0 : kernel α β) = 0 := by simp [compProd]

lemma compProd_apply [SFinite μ] [IsSFiniteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ := by
  simp_rw [compProd, kernel.compProd_apply _ _ _ hs, kernel.const_apply, kernel.prodMkLeft_apply']
  rfl

lemma compProd_apply_prod [SFinite μ] [IsSFiniteKernel κ]
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ ⊗ₘ κ) (s ×ˢ t) = ∫⁻ a in s, κ a t ∂μ := by
  rw [compProd_apply (hs.prod ht), ← lintegral_indicator _ hs]
  congr with a
  classical
  rw [Set.indicator_apply]
  split_ifs with ha <;> simp [ha]

lemma compProd_congr [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : κ =ᵐ[μ] η) : μ ⊗ₘ κ = μ ⊗ₘ η := by
  ext s hs
  have : (fun a ↦ κ a (Prod.mk a ⁻¹' s)) =ᵐ[μ] fun a ↦ η a (Prod.mk a ⁻¹' s) := by
    filter_upwards [h] with a ha using by rw [ha]
  rw [compProd_apply hs, lintegral_congr_ae this, compProd_apply hs]

lemma ae_compProd_of_ae_ae [SFinite μ] [IsSFiniteKernel κ] {p : α × β → Prop}
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b)) :
    ∀ᵐ x ∂(μ ⊗ₘ κ), p x :=
  kernel.ae_compProd_of_ae_ae hp h

lemma ae_ae_of_ae_compProd [SFinite μ] [IsSFiniteKernel κ] {p : α × β → Prop}
    (h : ∀ᵐ x ∂(μ ⊗ₘ κ), p x) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂κ a, p (a, b) := by
  convert kernel.ae_ae_of_ae_compProd h -- Much faster with `convert`

lemma ae_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {p : α × β → Prop}
    (hp : MeasurableSet {x | p x}) :
    (∀ᵐ x ∂(μ ⊗ₘ κ), p x) ↔ ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b) :=
  kernel.ae_compProd_iff hp

lemma compProd_add_left (μ ν : Measure α) [SFinite μ] [SFinite ν] (κ : kernel α β)
    [IsSFiniteKernel κ] :
    (μ + ν) ⊗ₘ κ = μ ⊗ₘ κ + ν ⊗ₘ κ := by
  rw [Measure.compProd, kernel.const_add, kernel.compProd_add_left]; rfl

lemma compProd_add_right (μ : Measure α) [SFinite μ] (κ η : kernel α β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ ⊗ₘ (κ + η) = μ ⊗ₘ κ + μ ⊗ₘ η := by
  rw [Measure.compProd, kernel.prodMkLeft_add, kernel.compProd_add_right]; rfl

section Integral

lemma lintegral_compProd [SFinite μ] [IsSFiniteKernel κ]
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd, kernel.lintegral_compProd _ _ _ hf]
  simp

lemma set_lintegral_compProd [SFinite μ] [IsSFiniteKernel κ]
    {f : α × β → ℝ≥0∞} (hf : Measurable f)
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ x in s ×ˢ t, f x ∂(μ ⊗ₘ κ) = ∫⁻ a in s, ∫⁻ b in t, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd, kernel.set_lintegral_compProd _ _ _ hf hs ht]
  simp

lemma integrable_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {E : Type*} [NormedAddCommGroup E]
    {f : α × β → E} (hf : AEStronglyMeasurable f (μ ⊗ₘ κ)) :
    Integrable f (μ ⊗ₘ κ) ↔
      (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) (κ x)) ∧
        Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂(κ x)) μ := by
  rw [Measure.compProd, ProbabilityTheory.integrable_compProd_iff hf]
  rfl

lemma integral_compProd [SFinite μ] [IsSFiniteKernel κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α × β → E} (hf : Integrable f (μ ⊗ₘ κ)) :
    ∫ x, f x ∂(μ ⊗ₘ κ) = ∫ a, ∫ b, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd, ProbabilityTheory.integral_compProd hf]
  simp

lemma setIntegral_compProd [SFinite μ] [IsSFiniteKernel κ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t)
    {f : α × β → E} (hf : IntegrableOn f (s ×ˢ t) (μ ⊗ₘ κ))  :
    ∫ x in s ×ˢ t, f x ∂(μ ⊗ₘ κ) = ∫ a in s, ∫ b in t, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd, ProbabilityTheory.setIntegral_compProd hs ht hf]
  simp

@[deprecated (since := "2024-04-17")]
alias set_integral_compProd := setIntegral_compProd

end Integral

lemma dirac_compProd_apply [MeasurableSingletonClass α] {a : α} [IsSFiniteKernel κ]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    (Measure.dirac a ⊗ₘ κ) s = κ a (Prod.mk a ⁻¹' s) := by
  rw [compProd_apply hs, lintegral_dirac]

lemma dirac_unit_compProd (κ : kernel Unit β) [IsSFiniteKernel κ] :
    Measure.dirac () ⊗ₘ κ = (κ ()).map (Prod.mk ()) := by
  ext s hs; rw [dirac_compProd_apply hs, Measure.map_apply measurable_prod_mk_left hs]

lemma dirac_unit_compProd_const (μ : Measure β) [IsFiniteMeasure μ] :
    Measure.dirac () ⊗ₘ kernel.const Unit μ = μ.map (Prod.mk ()) := by
  rw [dirac_unit_compProd, kernel.const_apply]

@[simp]
lemma snd_dirac_unit_compProd_const (μ : Measure β) [IsFiniteMeasure μ] :
    snd (Measure.dirac () ⊗ₘ kernel.const Unit μ) = μ := by
  rw [dirac_unit_compProd_const, snd, map_map measurable_snd measurable_prod_mk_left]
  simp

instance : SFinite (μ ⊗ₘ κ) := by rw [compProd]; infer_instance

instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (μ ⊗ₘ κ) := by
  rw [compProd]; infer_instance

instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (μ ⊗ₘ κ) := by
  rw [compProd]; infer_instance

end MeasureTheory.Measure
