/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Behavior of the Lebesgue integral under measure-preserving maps
-/

open ENNReal

namespace MeasureTheory.MeasurePreserving

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  {g : α → β} (hg : MeasurePreserving g μ ν)

protected theorem lintegral_map_equiv (f : β → ℝ≥0∞) (g : α ≃ᵐ β) (hg : MeasurePreserving g μ ν) :
    ∫⁻ a, f a ∂ν = ∫⁻ a, f (g a) ∂μ := by
  rw [← MeasureTheory.lintegral_map_equiv f g, hg.map_eq]

include hg

theorem lintegral_comp {f : β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν := by rw [← hg.map_eq, lintegral_map hf hg.measurable]

theorem lintegral_comp_emb (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞) :
    ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b ∂ν := by rw [← hg.map_eq, hge.lintegral_map]

theorem setLIntegral_comp_preimage
    {s : Set β} (hs : MeasurableSet s) {f : β → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν := by
  rw [← hg.map_eq, setLIntegral_map hs hf hg.measurable]

theorem setLIntegral_comp_preimage_emb (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞) (s : Set β) :
    ∫⁻ a in g ⁻¹' s, f (g a) ∂μ = ∫⁻ b in s, f b ∂ν := by
  rw [← hg.map_eq, hge.restrict_map, hge.lintegral_map]

theorem setLIntegral_comp_emb (hge : MeasurableEmbedding g) (f : β → ℝ≥0∞) (s : Set α) :
    ∫⁻ a in s, f (g a) ∂μ = ∫⁻ b in g '' s, f b ∂ν := by
  rw [← hg.setLIntegral_comp_preimage_emb hge, Set.preimage_image_eq _ hge.injective]

end MeasureTheory.MeasurePreserving
