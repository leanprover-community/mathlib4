/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Behavior of the Lebesgue integral under maps
-/

namespace MeasureTheory

open Set Filter ENNReal SimpleFunc

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}

section Map

open Measure

theorem lintegral_map {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f)
    (hg : Measurable g) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ := by
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  simp only [← Function.comp_apply (f := f) (g := g)]
  rw [lintegral_eq_iSup_eapprox_lintegral (hf.comp hg)]
  congr with n : 1
  convert SimpleFunc.lintegral_map _ hg
  ext1 x; simp only [eapprox_comp hf hg, coe_comp]

theorem lintegral_map' {f : β → ℝ≥0∞} {g : α → β}
    (hf : AEMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) :
    ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, f (g a) ∂μ :=
  calc
    ∫⁻ a, f a ∂Measure.map g μ = ∫⁻ a, hf.mk f a ∂Measure.map g μ :=
      lintegral_congr_ae hf.ae_eq_mk
    _ = ∫⁻ a, hf.mk f a ∂Measure.map (hg.mk g) μ := by
      congr 1
      exact Measure.map_congr hg.ae_eq_mk
    _ = ∫⁻ a, hf.mk f (hg.mk g a) ∂μ := lintegral_map hf.measurable_mk hg.measurable_mk
    _ = ∫⁻ a, hf.mk f (g a) ∂μ := lintegral_congr_ae <| hg.ae_eq_mk.symm.fun_comp _
    _ = ∫⁻ a, f (g a) ∂μ := lintegral_congr_ae (ae_eq_comp hg hf.ae_eq_mk.symm)

theorem lintegral_map_le (f : β → ℝ≥0∞) (g : α → β) :
    ∫⁻ a, f a ∂Measure.map g μ ≤ ∫⁻ a, f (g a) ∂μ := by
  by_cases hg : AEMeasurable g μ
  · rw [← iSup_lintegral_measurable_le_eq_lintegral]
    refine iSup₂_le fun i hi => iSup_le fun h'i => ?_
    rw [lintegral_map' hi.aemeasurable hg]
    exact lintegral_mono fun _ ↦ h'i _
  · simp [map_of_not_aemeasurable hg]

theorem lintegral_comp {f : β → ℝ≥0∞} {g : α → β} (hf : Measurable f)
    (hg : Measurable g) : lintegral μ (f ∘ g) = ∫⁻ a, f a ∂map g μ :=
  (lintegral_map hf hg).symm

theorem setLIntegral_map {f : β → ℝ≥0∞} {g : α → β} {s : Set β}
    (hs : MeasurableSet s) (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ y in s, f y ∂map g μ = ∫⁻ x in g ⁻¹' s, f (g x) ∂μ := by
  rw [restrict_map hg hs, lintegral_map hf hg]

theorem lintegral_indicator_const_comp {f : α → β} {s : Set β}
    (hf : Measurable f) (hs : MeasurableSet s) (c : ℝ≥0∞) :
    ∫⁻ a, s.indicator (fun _ => c) (f a) ∂μ = c * μ (f ⁻¹' s) := by
  erw [lintegral_comp (measurable_const.indicator hs) hf]
  rw [lintegral_indicator_const hs, Measure.map_apply hf hs]

/-- If `g : α → β` is a measurable embedding and `f : β → ℝ≥0∞` is any function (not necessarily
measurable), then `∫⁻ a, f a ∂(map g μ) = ∫⁻ a, f (g a) ∂μ`. Compare with `lintegral_map` which
applies to any measurable `g : α → β` but requires that `f` is measurable as well. -/
theorem _root_.MeasurableEmbedding.lintegral_map {g : α → β}
    (hg : MeasurableEmbedding g) (f : β → ℝ≥0∞) : ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ := by
  rw [lintegral, lintegral]
  refine le_antisymm (iSup₂_le fun f₀ hf₀ => ?_) (iSup₂_le fun f₀ hf₀ => ?_)
  · rw [SimpleFunc.lintegral_map _ hg.measurable]
    have : (f₀.comp g hg.measurable : α → ℝ≥0∞) ≤ f ∘ g := fun x => hf₀ (g x)
    exact le_iSup_of_le (comp f₀ g hg.measurable) (by exact le_iSup (α := ℝ≥0∞) _ this)
  · rw [← f₀.extend_comp_eq hg (const _ 0), ← SimpleFunc.lintegral_map, ←
      SimpleFunc.lintegral_eq_lintegral, ← lintegral]
    refine lintegral_mono_ae (hg.ae_map_iff.2 <| Eventually.of_forall fun x => ?_)
    exact (extend_apply _ _ _ _).trans_le (hf₀ _)

/-- The `lintegral` transforms appropriately under a measurable equivalence `g : α ≃ᵐ β`.
(Compare `lintegral_map`, which applies to a wider class of functions `g : α → β`, but requires
measurability of the function being integrated.) -/
theorem lintegral_map_equiv (f : β → ℝ≥0∞) (g : α ≃ᵐ β) :
    ∫⁻ a, f a ∂map g μ = ∫⁻ a, f (g a) ∂μ :=
  g.measurableEmbedding.lintegral_map f

theorem lintegral_subtype_comap {s : Set α} (hs : MeasurableSet s) (f : α → ℝ≥0∞) :
    ∫⁻ x : s, f x ∂(μ.comap (↑)) = ∫⁻ x in s, f x ∂μ := by
  rw [← (MeasurableEmbedding.subtype_coe hs).lintegral_map, map_comap_subtype_coe hs]

theorem setLIntegral_subtype {s : Set α} (hs : MeasurableSet s) (t : Set s) (f : α → ℝ≥0∞) :
    ∫⁻ x in t, f x ∂(μ.comap (↑)) = ∫⁻ x in (↑) '' t, f x ∂μ := by
  rw [(MeasurableEmbedding.subtype_coe hs).restrict_comap, lintegral_subtype_comap hs,
    restrict_restrict hs, inter_eq_right.2 (Subtype.coe_image_subset _ _)]

end Map

namespace MeasurePreserving

variable {g : α → β} (hg : MeasurePreserving g μ ν)

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

end MeasurePreserving

end MeasureTheory
