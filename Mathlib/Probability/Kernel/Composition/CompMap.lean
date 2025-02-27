/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Product and composition of kernels

We define
* the composition-product `κ ⊗ₖ η` of two s-finite kernels `κ : Kernel α β` and
  `η : Kernel (α × β) γ`, a kernel from `α` to `β × γ`.
* the map and comap of a kernel along a measurable function.
* the composition `η ∘ₖ κ` of kernels `κ : Kernel α β` and `η : Kernel β γ`, kernel from `α` to
  `γ`.
* the product `κ ×ₖ η` of s-finite kernels `κ : Kernel α β` and `η : Kernel α γ`,
  a kernel from `α` to `β × γ`.

A note on names:
The composition-product `Kernel α β → Kernel (α × β) γ → Kernel α (β × γ)` is named composition in
[kallenberg2021] and product on the wikipedia article on transition kernels.
Most papers studying categories of kernels call composition the map we call composition. We adopt
that convention because it fits better with the use of the name `comp` elsewhere in mathlib.

## Main definitions

Kernels built from other kernels:
* `compProd (κ : Kernel α β) (η : Kernel (α × β) γ) : Kernel α (β × γ)`: composition-product of 2
  s-finite kernels. We define a notation `κ ⊗ₖ η = compProd κ η`.
  `∫⁻ bc, f bc ∂((κ ⊗ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η (a, b)) ∂(κ a)`
* `map (κ : Kernel α β) (f : β → γ) : Kernel α γ`
  `∫⁻ c, g c ∂(map κ f a) = ∫⁻ b, g (f b) ∂(κ a)`
* `comap (κ : Kernel α β) (f : γ → α) (hf : Measurable f) : Kernel γ β`
  `∫⁻ b, g b ∂(comap κ f hf c) = ∫⁻ b, g b ∂(κ (f c))`
* `comp (η : Kernel β γ) (κ : Kernel α β) : Kernel α γ`: composition of 2 kernels.
  We define a notation `η ∘ₖ κ = comp η κ`.
  `∫⁻ c, g c ∂((η ∘ₖ κ) a) = ∫⁻ b, ∫⁻ c, g c ∂(η b) ∂(κ a)`
* `prod (κ : Kernel α β) (η : Kernel α γ) : Kernel α (β × γ)`: product of 2 s-finite kernels.
  `∫⁻ bc, f bc ∂((κ ×ₖ η) a) = ∫⁻ b, ∫⁻ c, f (b, c) ∂(η a) ∂(κ a)`

## Main statements

* `lintegral_compProd`, `lintegral_map`, `lintegral_comap`, `lintegral_comp`, `lintegral_prod`:
  Lebesgue integral of a function against a composition-product/map/comap/composition/product of
  kernels.
* Instances of the form `<class>.<operation>` where class is one of `IsMarkovKernel`,
  `IsFiniteKernel`, `IsSFiniteKernel` and operation is one of `compProd`, `map`, `comap`,
  `comp`, `prod`. These instances state that the three classes are stable by the various operations.

## Notations

* `κ ⊗ₖ η = ProbabilityTheory.Kernel.compProd κ η`
* `η ∘ₖ κ = ProbabilityTheory.Kernel.comp η κ`
* `κ ×ₖ η = ProbabilityTheory.Kernel.prod κ η`

-/


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {f : β → γ} {g : γ → α}

theorem deterministic_comp_eq_map (hf : Measurable f) (κ : Kernel α β) :
    deterministic f hf ∘ₖ κ = map κ f := by
  ext a s hs
  simp_rw [map_apply' _ hf _ hs, comp_apply' _ _ _ hs, deterministic_apply' hf _ hs,
    lintegral_indicator_const_comp hf hs, one_mul]

theorem comp_deterministic_eq_comap (κ : Kernel α β) (hg : Measurable g) :
    κ ∘ₖ deterministic g hg = comap κ g hg := by
  ext a s hs
  simp_rw [comap_apply' _ _ _ s, comp_apply' _ _ _ hs, deterministic_apply hg a,
    lintegral_dirac' _ (Kernel.measurable_coe κ hs)]

lemma deterministic_comp_deterministic (hf : Measurable f) (hg : Measurable g) :
    (deterministic g hg) ∘ₖ (deterministic f hf) = deterministic (g ∘ f) (hg.comp hf) := by
  ext; simp [comp_deterministic_eq_comap, comap_apply, deterministic_apply]

@[simp]
lemma comp_id (κ : Kernel α β) : κ ∘ₖ Kernel.id = κ := by
  rw [Kernel.id, comp_deterministic_eq_comap, comap_id]

@[simp]
lemma id_comp (κ : Kernel α β) : Kernel.id ∘ₖ κ = κ := by
  rw [Kernel.id, deterministic_comp_eq_map, map_id]

@[simp]
lemma id_map {f : α → β} (hf : Measurable f) : Kernel.id.map f = deterministic f hf := by
  rw [← deterministic_comp_eq_map, comp_id]

@[simp]
lemma id_comap {f : α → β} (hf : Measurable f) : Kernel.id.comap f hf = deterministic f hf := by
  rw [← comp_deterministic_eq_comap, id_comp]

lemma deterministic_map {f : α → β} (hf : Measurable f) {g : β → γ} (hg : Measurable g) :
    (deterministic f hf).map g = deterministic (g ∘ f) (hg.comp hf) := by
  rw [← id_map, ← map_comp_right _ hf hg, id_map]

@[simp]
lemma swap_swap : (swap α β) ∘ₖ (swap β α) = Kernel.id := by
  simp_rw [swap, Kernel.deterministic_comp_deterministic, Prod.swap_swap_eq, Kernel.id]

lemma swap_comp_eq_map {κ : Kernel α (β × γ)} : (swap β γ) ∘ₖ κ = κ.map Prod.swap := by
  rw [swap, deterministic_comp_eq_map]

lemma map_comp (κ : Kernel α β) (η : Kernel β γ) (f : γ → δ) :
    (η ∘ₖ κ).map f = (η.map f) ∘ₖ κ := by
  by_cases hf : Measurable f
  · ext a s hs
    rw [map_apply' _ hf _ hs, comp_apply', comp_apply' _ _ _ hs]
    · simp_rw [map_apply' _ hf _ hs]
    · exact hf hs
  · simp [map_of_not_measurable _ hf]

lemma comp_map (κ : Kernel α β) (η : Kernel γ δ) {f : β → γ} (hf : Measurable f) :
    η ∘ₖ (κ.map f) = (η.comap f hf) ∘ₖ κ := by
  ext x s ms
  rw [comp_apply' _ _ _ ms, lintegral_map _ hf _ (η.measurable_coe ms), comp_apply' _ _ _ ms]
  simp_rw [comap_apply']

lemma fst_comp (κ : Kernel α β) (η : Kernel β (γ × δ)) : (η ∘ₖ κ).fst = η.fst ∘ₖ κ := by
  simp [fst_eq, map_comp κ η _]

lemma snd_comp (κ : Kernel α β) (η : Kernel β (γ × δ)) : (η ∘ₖ κ).snd = η.snd ∘ₖ κ := by
  simp_rw [snd_eq, map_comp κ η _]

end Kernel
end ProbabilityTheory
