/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Lemmas about the composition of a measure and a kernel

Basic lemmas about the composition `κ ∘ₘ μ` of a kernel `κ` and a measure `μ`.

-/

open scoped ENNReal

open ProbabilityTheory MeasureTheory

namespace MeasureTheory.Measure

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {μ ν : Measure α} {κ η : Kernel α β}

lemma comp_assoc {η : Kernel β γ} : η ∘ₘ (κ ∘ₘ μ) = (η ∘ₖ κ) ∘ₘ μ :=
  Measure.bind_bind κ.aemeasurable η.aemeasurable

/-- This lemma allows to rewrite the compostion of a measure and a kernel as the composition
of two kernels, which allows to transfer properties of `∘ₖ` to `∘ₘ`. -/
lemma comp_eq_comp_const_apply : κ ∘ₘ μ = (κ ∘ₖ (Kernel.const Unit μ)) () := by
  rw [Kernel.comp_apply, Kernel.const_apply]

lemma comp_eq_sum_of_countable [Countable α] [MeasurableSingletonClass α] :
    κ ∘ₘ μ = Measure.sum (fun ω ↦ μ {ω} • κ ω) := by
  ext s hs
  rw [Measure.sum_apply _ hs, Measure.bind_apply hs (by fun_prop)]
  simp [lintegral_countable', mul_comm]

@[simp]
lemma snd_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).snd = κ ∘ₘ μ := by
  ext s hs
  rw [bind_apply hs κ.aemeasurable, snd_apply hs, compProd_apply]
  · rfl
  · exact measurable_snd hs

lemma ae_ae_of_ae_comp {p : β → Prop} (h : ∀ᵐ ω ∂(κ ∘ₘ μ), p ω) :
    ∀ᵐ ω' ∂μ, ∀ᵐ ω ∂(κ ω'), p ω := by
  rw [comp_eq_comp_const_apply] at h
  exact Kernel.ae_ae_of_ae_comp h

instance [SFinite μ] [IsSFiniteKernel κ] : SFinite (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance

instance [IsFiniteMeasure μ] [IsFiniteKernel κ] : IsFiniteMeasure (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance

instance [IsProbabilityMeasure μ] [IsMarkovKernel κ] : IsProbabilityMeasure (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance

instance [IsZeroOrProbabilityMeasure μ] [IsZeroOrMarkovKernel κ] :
    IsZeroOrProbabilityMeasure (κ ∘ₘ μ) := by
  rw [← snd_compProd]; infer_instance

lemma map_comp (μ : Measure α) (κ : Kernel α β) {f : β → γ} (hf : Measurable f) :
    (κ ∘ₘ μ).map f = (κ.map f) ∘ₘ μ := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.bind_apply (hf hs) κ.aemeasurable,
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Kernel.map_apply' _ hf _ hs]

section CompProd

lemma compProd_eq_comp_prod (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    μ ⊗ₘ κ = (Kernel.id ×ₖ κ) ∘ₘ μ := by
  rw [compProd, Kernel.compProd_prodMkLeft_eq_comp]
  rfl

lemma compProd_id_eq_copy_comp [SFinite μ] : μ ⊗ₘ Kernel.id = Kernel.copy α ∘ₘ μ := by
  rw [compProd_id, Kernel.copy, deterministic_comp_eq_map]

lemma comp_compProd_comm {η : Kernel (α × β) γ} [SFinite μ] [IsSFiniteKernel η] :
    η ∘ₘ (μ ⊗ₘ κ) = ((κ ⊗ₖ η) ∘ₘ μ).snd := by
  by_cases hκ : IsSFiniteKernel κ; swap
  · simp [compProd_of_not_isSFiniteKernel _ _ hκ,
      Kernel.compProd_of_not_isSFiniteKernel_left _ _ hκ]
  ext s hs
  rw [Measure.bind_apply hs η.aemeasurable, Measure.snd_apply hs,
    Measure.bind_apply _ (Kernel.aemeasurable _), Measure.lintegral_compProd (η.measurable_coe hs)]
  swap; · exact measurable_snd hs
  congr with a
  rw [Kernel.compProd_apply]
  · rfl
  · exact measurable_snd hs

@[simp]
lemma prodMkLeft_comp_compProd {η : Kernel β γ} [SFinite μ] [IsSFiniteKernel κ] :
    (η.prodMkLeft α) ∘ₘ μ ⊗ₘ κ = η ∘ₘ κ ∘ₘ μ := by
  rw [← snd_compProd μ κ, Kernel.prodMkLeft, snd, ← deterministic_comp_eq_map measurable_snd,
    comp_assoc, Kernel.comp_deterministic_eq_comap]

end CompProd

section AddSMul

@[simp]
lemma comp_add : κ ∘ₘ (μ + ν) = κ ∘ₘ μ + κ ∘ₘ ν := by
  simp_rw [comp_eq_comp_const_apply, Kernel.const_add, Kernel.comp_add_right, Kernel.add_apply]

lemma add_comp : (κ + η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ := by
  simp_rw [comp_eq_comp_const_apply, Kernel.comp_add_left, Kernel.add_apply]

/-- Same as `add_comp` except that it uses `⇑κ + ⇑η` instead of `⇑(κ + η)` in order to have
a simp-normal form on the left of the equality. -/
@[simp]
lemma add_comp' : (⇑κ + ⇑η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ := by rw [← Kernel.coe_add, add_comp]

@[simp]
lemma comp_smul (a : ℝ≥0∞) : κ ∘ₘ (a • μ) = a • (κ ∘ₘ μ) := by
  ext s hs
  simp only [bind_apply hs κ.aemeasurable, lintegral_smul_measure, smul_apply, smul_eq_mul]

end AddSMul

section AbsolutelyContinuous

lemma AbsolutelyContinuous.comp_right (hμν : μ ≪ ν) (κ : Kernel α γ) :
    κ ∘ₘ μ ≪ κ ∘ₘ ν := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hs)] at hs_zero ⊢
  exact hμν.ae_eq hs_zero

lemma AbsolutelyContinuous.comp_left (μ : Measure α) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ μ := by
  refine Measure.AbsolutelyContinuous.mk fun s hs hs_zero ↦ ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_eq_zero_iff (Kernel.measurable_coe _ hs)] at hs_zero ⊢
  filter_upwards [hs_zero, hκη] with a ha_zero ha_ac using ha_ac ha_zero

lemma AbsolutelyContinuous.comp (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ ν :=
  (AbsolutelyContinuous.comp_left μ hκη).trans (hμν.comp_right η)

lemma absolutelyContinuous_comp_of_countable [Countable α] [MeasurableSingletonClass α] :
    ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ := by
  rw [Measure.comp_eq_sum_of_countable, ae_iff_of_countable]
  exact fun ω hμω ↦ Measure.absolutelyContinuous_sum_right ω (Measure.absolutelyContinuous_smul hμω)

end AbsolutelyContinuous

end MeasureTheory.Measure
