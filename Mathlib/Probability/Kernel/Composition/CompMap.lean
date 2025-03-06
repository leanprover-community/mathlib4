/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Lemmas about compositions and maps of kernels

This file contains results that use both the composition of kernels and the map of a kernel by a
function.

Map and comap are particular cases of composition: they correspond to composition with
a deterministic kernel. See `deterministic_comp_eq_map` and `comp_deterministic_eq_comap`.

-/


open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

namespace Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}


variable {γ δ : Type*} {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ} {f : β → γ} {g : γ → α}

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
