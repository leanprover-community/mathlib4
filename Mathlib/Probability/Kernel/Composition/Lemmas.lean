/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-!
# Lemmas relating different ways to compose measures and kernels

This file contains lemmas about the composition of measures and kernels that do not fit in any of
the other files in this directory, because they involve several types of compositions/products.

-/

public section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
  {μ : Measure α} {ν : Measure β} {κ : Kernel α β}

namespace ProbabilityTheory.Kernel

/-- The composition of two product kernels `(ξ ×ₖ η') ∘ₖ (κ ×ₖ ζ)` is the product of the
compositions `(ξ ∘ₖ (κ ×ₖ ζ)) ×ₖ (η' ∘ₖ (κ ×ₖ ζ))`, if `ζ` is deterministic (of the form
`.deterministic f hf`) and `η'` does not depend on the output of `κ`.
That is, `η'` has the form `η.prodMkLeft β` for a kernel `η`.

If `κ` was deterministic, this would be true even if `η.prodMkLeft β` was a more general
kernel since `κ ×ₖ Kernel.deterministic f hf` would be deterministic and commute with copying.
Here `κ` is not deterministic, but it is discarded in one branch of the copy. -/
lemma prod_prodMkLeft_comp_prod_deterministic {β' ε : Type*}
    {mβ' : MeasurableSpace β'} {mε : MeasurableSpace ε}
    (κ : Kernel γ β) [IsSFiniteKernel κ] (η : Kernel ε β') [IsSFiniteKernel η]
    (ξ : Kernel (β × ε) δ) [IsSFiniteKernel ξ] {f : γ → ε} (hf : Measurable f) :
    (ξ ×ₖ η.prodMkLeft β) ∘ₖ (κ ×ₖ deterministic f hf)
      = (ξ ∘ₖ (κ ×ₖ deterministic f hf)) ×ₖ (η ∘ₖ deterministic f hf) := by
  ext ω s hs
  rw [prod_apply' _ _ _ hs, comp_apply' _ _ _ hs, lintegral_prod_deterministic,
    lintegral_comp, lintegral_prod_deterministic]
  · congr with b
    rw [prod_apply' _ _ _ hs, prodMkLeft_apply, comp_deterministic_eq_comap, comap_apply]
  · exact (measurable_measure_prodMk_left hs).lintegral_kernel
  · exact measurable_measure_prodMk_left hs
  · exact Kernel.measurable_coe _ hs

/-- The composition of two product kernels `(ξ ×ₖ η') ∘ₖ (ζ ×ₖ κ)` is the product of the
compositions, `(ξ ∘ₖ (ζ ×ₖ κ)) ×ₖ (η' ∘ₖ (ζ ×ₖ κ))`, if `ζ` is deterministic (of the form
`.deterministic f hf`) and `η'` does not depend on the output of `κ`.
That is, `η'` has the form `η.prodMkRight β` for a kernel `η`.

If `κ` was deterministic, this would be true even if `η.prodMkRight β` was a more general
kernel since `Kernel.deterministic f hf ×ₖ κ` would be deterministic and commute with copying.
Here `κ` is not deterministic, but it is discarded in one branch of the copy. -/
lemma prod_prodMkRight_comp_deterministic_prod {β' ε : Type*}
    {mβ' : MeasurableSpace β'} {mε : MeasurableSpace ε}
    (κ : Kernel γ β) [IsSFiniteKernel κ] (η : Kernel ε β') [IsSFiniteKernel η]
    (ξ : Kernel (ε × β) δ) [IsSFiniteKernel ξ] {f : γ → ε} (hf : Measurable f) :
    (ξ ×ₖ η.prodMkRight β) ∘ₖ (deterministic f hf ×ₖ κ)
      = (ξ ∘ₖ (deterministic f hf ×ₖ κ)) ×ₖ (η ∘ₖ deterministic f hf) := by
  ext ω s hs
  rw [prod_apply' _ _ _ hs, comp_apply' _ _ _ hs, lintegral_deterministic_prod,
    lintegral_comp, lintegral_deterministic_prod]
  · congr with b
    rw [prod_apply' _ _ _ hs, prodMkRight_apply, comp_deterministic_eq_comap, comap_apply]
  · exact (measurable_measure_prodMk_left hs).lintegral_kernel
  · exact measurable_measure_prodMk_left hs
  · exact Kernel.measurable_coe _ hs

/-- If `η ∘ₖ κ` is a deterministic kernel given by `f`, then `η x` is almost everywhere the
Dirac measure at `f a`. -/
lemma comp_eq_deterministic_ae_eq_dirac {η : Kernel β α} [IsMarkovKernel η] {f : α → α}
    (hf : Measurable f) (h : η ∘ₖ κ = deterministic f hf) (a : α) {s : Set α}
    (hs : MeasurableSet s) : ∀ᵐ x ∂(κ a), η x s = Measure.dirac (f a) s := by
  have hg_eq : ∫⁻ x, (η x) s ∂κ a = Measure.dirac (f a) s := by
    rw [← comp_apply' _ _ _ hs, h, deterministic_apply]
  simp only [Measure.dirac_apply' _ hs] at ⊢ hg_eq
  by_cases hfa : (f a) ∈ s
  · simp only [hfa, Set.indicator_of_mem, Pi.one_apply] at ⊢ hg_eq
    replace hg_eq : ∫⁻ x, (1 - (η x) s) ∂κ a = 0 := by
      calc
      _ =∫⁻ x, (η x) sᶜ ∂κ a := by
        congr with x
        rw [measure_compl hs (by simp)]
        simp
      _ = (η ∘ₖ κ) a sᶜ := by
        rw [η.comp_apply' _ _ hs.compl]
      _ = 0 := by
        simp [h, deterministic_apply' hf _ hs.compl, hfa]
    rw [lintegral_eq_zero_iff'] at hg_eq
    · filter_upwards [hg_eq] with y hy
      rw [Pi.zero_apply, tsub_eq_zero_iff_le] at hy
      exact one_le_prob_iff.mp hy
    have := η.measurable_coe hs
    fun_prop
  · simp only [hfa, not_false_eq_true, Set.indicator_of_notMem] at ⊢ hg_eq
    rwa [lintegral_eq_zero_iff' ((η.measurable_coe hs).aemeasurable)] at hg_eq

lemma parallelComp_id_comp_copy_comp [IsMarkovKernel κ] {η : Kernel β α} [IsMarkovKernel η]
    (h : ∃ f, ∃ (hf : Measurable f), η ∘ₖ κ = deterministic f hf) :
    η ∘ₖ κ ∥ₖ κ ∘ₖ copy α = η ∥ₖ Kernel.id ∘ₖ copy β ∘ₖ κ := by
  simp only [parallelComp_comp_copy]
  ext x : 1
  rw [prod_apply]
  refine Measure.prod_eq fun s₁ s₂ hs₁ hs₂ ↦ ?_
  obtain ⟨f, hf, h⟩ := h
  rw [h, comp_apply, Measure.bind_apply, deterministic_apply]
  · suffices ∀ᵐ a ∂(κ x), (η ×ₖ Kernel.id) a (s₁ ×ˢ s₂) =
        (Measure.dirac (f x)) s₁ * (Measure.dirac a) s₂ by
      rw [MeasureTheory.lintegral_congr_ae this]
      simp [lintegral_const_mul', hs₂]
    filter_upwards [comp_eq_deterministic_ae_eq_dirac hf h x hs₁] with a ha
    rw [prod_apply_prod, ha, Kernel.id_apply]
  · exact hs₁.prod hs₂
  · fun_prop

end ProbabilityTheory.Kernel

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

lemma parallelComp_comp_compProd [IsSFiniteKernel κ] {η : Kernel β γ} [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ η) ∘ₘ (μ ⊗ₘ κ) = μ ⊗ₘ (η ∘ₖ κ) := by
  by_cases hμ : SFinite μ
  swap; · simp [hμ]
  rw [Measure.compProd_eq_comp_prod, Measure.compProd_eq_comp_prod, Measure.comp_assoc,
    Kernel.parallelComp_comp_prod, Kernel.id_comp]

lemma compProd_map [SFinite μ] [IsSFiniteKernel κ] {f : β → γ} (hf : Measurable f) :
    μ ⊗ₘ (κ.map f) = (μ ⊗ₘ κ).map (Prod.map id f) := by
  calc μ ⊗ₘ (κ.map f)
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.id ×ₖ κ) ∘ₘ μ := by
    rw [comp_assoc, Kernel.parallelComp_comp_prod, compProd_eq_comp_prod,
      Kernel.id_comp, Kernel.deterministic_comp_eq_map]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (μ ⊗ₘ κ) := by rw [compProd_eq_comp_prod]
  _ = (μ ⊗ₘ κ).map (Prod.map id f) := by
    rw [Kernel.id, Kernel.deterministic_parallelComp_deterministic, deterministic_comp_eq_map]

end MeasureTheory.Measure
