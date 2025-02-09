/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

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
  Measure.bind_bind κ.measurable η.measurable

@[simp]
lemma snd_compProd (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    (μ ⊗ₘ κ).snd = κ ∘ₘ μ := by
  ext s hs
  rw [bind_apply hs κ.measurable, snd_apply hs, compProd_apply]
  · rfl
  · exact measurable_snd hs

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
  rw [Measure.map_apply hf hs, Measure.bind_apply (hf hs) κ.measurable,
    Measure.bind_apply hs (Kernel.measurable _)]
  simp_rw [Kernel.map_apply' _ hf _ hs]

section CompProd

lemma compProd_eq_comp_prod (μ : Measure α) [SFinite μ] (κ : Kernel α β) [IsSFiniteKernel κ] :
    μ ⊗ₘ κ = (Kernel.id ×ₖ κ) ∘ₘ μ := by
  rw [compProd, Kernel.compProd_prodMkLeft_eq_comp]
  rfl

lemma compProd_id_eq_copy_comp [SFinite μ] : μ ⊗ₘ Kernel.id = Kernel.copy α ∘ₘ μ := by
  rw [compProd_id, Kernel.copy, deterministic_comp_eq_map]

end CompProd

section AddSMul

@[simp]
lemma comp_add [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] :
    κ ∘ₘ (μ + ν) = κ ∘ₘ μ + κ ∘ₘ ν := by
  simp_rw [← snd_compProd, compProd_add_left]
  simp

lemma add_comp [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (κ + η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ := by
  simp_rw [← snd_compProd, compProd_add_right]
  simp

/-- Same as `add_comp` except that it uses `⇑κ + ⇑η` instead of `⇑(κ + η)` in order to have
a simp-normal form on the left of the equality. -/
@[simp]
lemma add_comp' [SFinite μ] [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (⇑κ + ⇑η) ∘ₘ μ = κ ∘ₘ μ + η ∘ₘ μ := by rw [← Kernel.coe_add, add_comp]

lemma comp_smul (a : ℝ≥0∞) : κ ∘ₘ (a • μ) = a • (κ ∘ₘ μ) := by
  ext s hs
  simp only [bind_apply hs κ.measurable, lintegral_smul_measure, smul_apply, smul_eq_mul]

end AddSMul

section AbsolutelyContinuous

variable [SFinite μ] [SFinite ν] [IsSFiniteKernel κ] [IsSFiniteKernel η]

lemma AbsolutelyContinuous.comp (hμν : μ ≪ ν) (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ ν := by
  simp_rw [← snd_compProd, Measure.snd]
  exact (hμν.compProd hκη).map measurable_snd

lemma AbsolutelyContinuous.comp_right (hμν : μ ≪ ν) (κ : Kernel α γ) [IsSFiniteKernel κ]  :
    κ ∘ₘ μ ≪ κ ∘ₘ ν :=
  hμν.comp (ae_of_all μ fun _ _ a ↦ a)

lemma AbsolutelyContinuous.comp_left (μ : Measure α) [SFinite μ] (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    κ ∘ₘ μ ≪ η ∘ₘ μ :=
  μ.absolutelyContinuous_refl.comp hκη

end AbsolutelyContinuous

end MeasureTheory.Measure
