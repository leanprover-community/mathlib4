/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.IntegralCompProd

/-!
# Composition-Product of a measure and a kernel

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

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

/-- The composition-product of a measure and a kernel. -/
noncomputable
def compProd (μ : Measure α) (κ : Kernel α β) : Measure (α × β) :=
  (Kernel.const Unit μ ⊗ₖ Kernel.prodMkLeft Unit κ) ()

@[inherit_doc]
scoped[ProbabilityTheory] infixl:100 " ⊗ₘ " => MeasureTheory.Measure.compProd

lemma compProd_of_not_sfinite (μ : Measure α) (κ : Kernel α β) (h : ¬ SFinite μ) :
    μ ⊗ₘ κ = 0 := by
  rw [compProd, Kernel.compProd_of_not_isSFiniteKernel_left, Kernel.zero_apply]
  rwa [Kernel.isSFiniteKernel_const]

lemma compProd_of_not_isSFiniteKernel (μ : Measure α) (κ : Kernel α β) (h : ¬ IsSFiniteKernel κ) :
    μ ⊗ₘ κ = 0 := by
  rw [compProd, Kernel.compProd_of_not_isSFiniteKernel_right, Kernel.zero_apply]
  rwa [Kernel.isSFiniteKernel_prodMkLeft_unit]

@[simp] lemma compProd_zero_left (κ : Kernel α β) : (0 : Measure α) ⊗ₘ κ = 0 := by simp [compProd]
@[simp] lemma compProd_zero_right (μ : Measure α) : μ ⊗ₘ (0 : Kernel α β) = 0 := by simp [compProd]

lemma compProd_apply [SFinite μ] [IsSFiniteKernel κ] {s : Set (α × β)} (hs : MeasurableSet s) :
    (μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ := by
  simp_rw [compProd, Kernel.compProd_apply hs, Kernel.const_apply, Kernel.prodMkLeft_apply']
  rfl

lemma compProd_apply_prod [SFinite μ] [IsSFiniteKernel κ]
    {s : Set α} {t : Set β} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ ⊗ₘ κ) (s ×ˢ t) = ∫⁻ a in s, κ a t ∂μ := by
  rw [compProd_apply (hs.prod ht), ← lintegral_indicator hs]
  congr with a
  classical
  rw [Set.indicator_apply]
  split_ifs with ha <;> simp [ha]

lemma compProd_congr [IsSFiniteKernel κ] [IsSFiniteKernel η]
    (h : κ =ᵐ[μ] η) : μ ⊗ₘ κ = μ ⊗ₘ η := by
  by_cases hμ : SFinite μ
  · ext s hs
    have : (fun a ↦ κ a (Prod.mk a ⁻¹' s)) =ᵐ[μ] fun a ↦ η a (Prod.mk a ⁻¹' s) := by
      filter_upwards [h] with a ha using by rw [ha]
    rw [compProd_apply hs, lintegral_congr_ae this, compProd_apply hs]
  · simp [compProd_of_not_sfinite _ _ hμ]

lemma ae_compProd_of_ae_ae {p : α × β → Prop}
    (hp : MeasurableSet {x | p x}) (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b)) :
    ∀ᵐ x ∂(μ ⊗ₘ κ), p x :=
  Kernel.ae_compProd_of_ae_ae hp h

lemma ae_ae_of_ae_compProd [SFinite μ] [IsSFiniteKernel κ] {p : α × β → Prop}
    (h : ∀ᵐ x ∂(μ ⊗ₘ κ), p x) :
    ∀ᵐ a ∂μ, ∀ᵐ b ∂κ a, p (a, b) := by
  convert Kernel.ae_ae_of_ae_compProd h -- Much faster with `convert`

lemma ae_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {p : α × β → Prop}
    (hp : MeasurableSet {x | p x}) :
    (∀ᵐ x ∂(μ ⊗ₘ κ), p x) ↔ ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), p (a, b) :=
  Kernel.ae_compProd_iff hp

lemma compProd_add_left (μ ν : Measure α) [SFinite μ] [SFinite ν] (κ : Kernel α β) :
    (μ + ν) ⊗ₘ κ = μ ⊗ₘ κ + ν ⊗ₘ κ := by
  by_cases hκ : IsSFiniteKernel κ
  · simp_rw [Measure.compProd, Kernel.const_add, Kernel.compProd_add_left, Kernel.add_apply]
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ]

lemma compProd_add_right (μ : Measure α) (κ η : Kernel α β)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    μ ⊗ₘ (κ + η) = μ ⊗ₘ κ + μ ⊗ₘ η := by
  by_cases hμ : SFinite μ
  · simp_rw [Measure.compProd, Kernel.prodMkLeft_add, Kernel.compProd_add_right, Kernel.add_apply]
  · simp [compProd_of_not_sfinite _ _ hμ]

section Integral

lemma lintegral_compProd [SFinite μ] [IsSFiniteKernel κ]
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd, Kernel.lintegral_compProd _ _ _ hf]
  simp

lemma setLIntegral_compProd [SFinite μ] [IsSFiniteKernel κ]
    {f : α × β → ℝ≥0∞} (hf : Measurable f)
    {s : Set α} (hs : MeasurableSet s) {t : Set β} (ht : MeasurableSet t) :
    ∫⁻ x in s ×ˢ t, f x ∂(μ ⊗ₘ κ) = ∫⁻ a in s, ∫⁻ b in t, f (a, b) ∂(κ a) ∂μ := by
  rw [compProd, Kernel.setLIntegral_compProd _ _ _ hf hs ht]
  simp

@[deprecated (since := "2024-06-29")]
alias set_lintegral_compProd := setLIntegral_compProd

lemma integrable_compProd_iff [SFinite μ] [IsSFiniteKernel κ] {E : Type*} [NormedAddCommGroup E]
    {f : α × β → E} (hf : AEStronglyMeasurable f (μ ⊗ₘ κ)) :
    Integrable f (μ ⊗ₘ κ) ↔
      (∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) (κ x)) ∧
        Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂(κ x)) μ := by
  simp_rw [Measure.compProd, ProbabilityTheory.integrable_compProd_iff hf, Kernel.prodMkLeft_apply,
    Kernel.const_apply]

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

lemma dirac_unit_compProd (κ : Kernel Unit β) [IsSFiniteKernel κ] :
    Measure.dirac () ⊗ₘ κ = (κ ()).map (Prod.mk ()) := by
  ext s hs; rw [dirac_compProd_apply hs, Measure.map_apply measurable_prod_mk_left hs]

lemma dirac_unit_compProd_const (μ : Measure β) [IsFiniteMeasure μ] :
    Measure.dirac () ⊗ₘ Kernel.const Unit μ = μ.map (Prod.mk ()) := by
  rw [dirac_unit_compProd, Kernel.const_apply]

@[simp]
lemma snd_dirac_unit_compProd_const (μ : Measure β) [IsFiniteMeasure μ] :
    snd (Measure.dirac () ⊗ₘ Kernel.const Unit μ) = μ := by
  rw [dirac_unit_compProd_const, snd, map_map measurable_snd measurable_prod_mk_left]
  simp

instance : SFinite (μ ⊗ₘ κ) := by rw [compProd]; infer_instance

instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (μ ⊗ₘ κ) := by
  rw [compProd]; infer_instance

instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (μ ⊗ₘ κ) := by
  rw [compProd]; infer_instance

section AbsolutelyContinuous

lemma absolutelyContinuous_compProd_left [SFinite ν] (hμν : μ ≪ ν) (κ : Kernel α β) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ κ := by
  by_cases hκ : IsSFiniteKernel κ
  · have : SFinite μ := sFinite_of_absolutelyContinuous hμν
    refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
    rw [Measure.compProd_apply hs, lintegral_eq_zero_iff (Kernel.measurable_kernel_prod_mk_left hs)]
      at hs_zero ⊢
    exact hμν.ae_eq hs_zero
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ]

lemma absolutelyContinuous_compProd_right [SFinite μ] [IsSFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
  by_cases hκ : IsSFiniteKernel κ
  · refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
    rw [Measure.compProd_apply hs, lintegral_eq_zero_iff (Kernel.measurable_kernel_prod_mk_left hs)]
      at hs_zero ⊢
    filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zero
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ]

lemma absolutelyContinuous_compProd [SFinite ν] [IsSFiniteKernel η]
    (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    μ ⊗ₘ κ ≪ ν ⊗ₘ η :=
  have : SFinite μ := sFinite_of_absolutelyContinuous hμν
  (Measure.absolutelyContinuous_compProd_right hκη).trans
    (Measure.absolutelyContinuous_compProd_left hμν _)

lemma absolutelyContinuous_of_compProd [SFinite μ] [IsSFiniteKernel κ] [h_zero : ∀ a, NeZero (κ a)]
    (h : μ ⊗ₘ κ ≪ ν ⊗ₘ η) :
    μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk (fun s hs hs0 ↦ ?_)
  have h1 : (ν ⊗ₘ η) (s ×ˢ Set.univ) = 0 := by
    by_cases hν : SFinite ν
    swap; · simp [compProd_of_not_sfinite _ _ hν]
    by_cases hη : IsSFiniteKernel η
    swap; · simp [compProd_of_not_isSFiniteKernel _ _ hη]
    rw [Measure.compProd_apply_prod hs MeasurableSet.univ]
    exact setLIntegral_measure_zero _ _ hs0
  have h2 : (μ ⊗ₘ κ) (s ×ˢ Set.univ) = 0 := h h1
  rw [Measure.compProd_apply_prod hs MeasurableSet.univ, lintegral_eq_zero_iff] at h2
  swap; · exact Kernel.measurable_coe _ MeasurableSet.univ
  by_contra hμs
  have : Filter.NeBot (ae (μ.restrict s)) := by simp [hμs]
  obtain ⟨a, ha⟩ : ∃ a, κ a Set.univ = 0 := h2.exists
  refine absurd ha ?_
  simp only [Measure.measure_univ_eq_zero]
  exact (h_zero a).out

end AbsolutelyContinuous

end MeasureTheory.Measure
