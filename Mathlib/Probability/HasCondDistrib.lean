/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/

module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Kernel.CondDistrib

/-!
# A predicate for having a specified conditional distribution

We introduce a predicate `HasCondDistrib Y X κ P` stating that the conditional distribution of `Y`
given `X` under the measure `P` is equal to the kernel `κ`. We also require that `Y` and `X` are
a.e. measurable, which is necessary for the conditional distribution to be well-defined.

## Main definitions

* `HasCondDistrib Y X κ P` : predicate stating that the conditional distribution of `Y` given `X`
  under the measure `P` is equal to the kernel `κ`.

-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {𝓧 𝓨 𝓩 Ω Ω' : Type*}
  {m𝓧 : MeasurableSpace 𝓧} {m𝓨 : MeasurableSpace 𝓨} {m𝓩 : MeasurableSpace 𝓩}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [Nonempty Ω]
  {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] [Nonempty Ω']
  {P : Measure 𝓧} [IsFiniteMeasure P] {X : 𝓧 → 𝓨} {Y : 𝓧 → Ω} {κ : Kernel 𝓨 Ω}

/-- Predicate stating that the conditional distribution of `Y` given `X` under the measure `P`
is equal to the kernel `κ`. -/
structure HasCondDistrib (Y : 𝓧 → Ω) (X : 𝓧 → 𝓨) (κ : Kernel 𝓨 Ω)
    (P : Measure 𝓧) [IsFiniteMeasure P] : Prop where
  aemeasurable_fst : AEMeasurable Y P := by fun_prop
  aemeasurable_snd : AEMeasurable X P := by fun_prop
  condDistrib_eq : condDistrib Y X P =ᵐ[P.map X] κ

attribute [fun_prop] HasCondDistrib.aemeasurable_fst HasCondDistrib.aemeasurable_snd

lemma HasCondDistrib.hasLaw_of_const {P : Measure 𝓧} [IsProbabilityMeasure P]
    {Q : Measure Ω} [SFinite Q]
    (h : HasCondDistrib Y X (Kernel.const 𝓨 Q) P) :
    HasLaw Y Q P := by
  obtain ⟨hY, hX, h⟩ := h
  refine ⟨hY, ?_⟩
  have h_snd : (P.map (fun ω ↦ (X ω, Y ω))).snd = Q := by
    have h_map : P.map (fun ω ↦ (X ω, Y ω)) = (P.map X) ⊗ₘ (Kernel.const _ Q) :=
      (compProd_map_condDistrib hY).symm.trans (Measure.compProd_congr h)
    rw [h_map, Measure.snd_compProd]
    simp [Measure.map_apply_of_aemeasurable hX]
  rwa [Measure.snd_map_prodMk₀ hX] at h_snd

lemma HasCondDistrib.comp (h : HasCondDistrib Y X κ P) {f : Ω → Ω'} (hf : Measurable f) :
    HasCondDistrib (fun ω ↦ f (Y ω)) X (κ.map f) P where
  aemeasurable_fst := by have := h.aemeasurable_fst; fun_prop
  aemeasurable_snd := by have := h.aemeasurable_snd; fun_prop
  condDistrib_eq := by
    have h_comp := condDistrib_comp X (Y := Y) (f := f) (mβ := m𝓨) h.aemeasurable_fst hf
    refine h_comp.trans ?_
    have h' := h.condDistrib_eq
    filter_upwards [h'] with ω hω
    rw [Kernel.map_apply _ hf, hω, Kernel.map_apply _ hf]

lemma HasCondDistrib.fst {Y : 𝓧 → Ω × Ω'} {κ : Kernel 𝓨 (Ω × Ω')} (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω ↦ (Y ω).1) X κ.fst P := by
  rw [Kernel.fst_eq]
  exact HasCondDistrib.comp h measurable_fst

lemma HasCondDistrib.snd {Y : 𝓧 → Ω × Ω'} {κ : Kernel 𝓨 (Ω × Ω')} (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω ↦ (Y ω).2) X κ.snd P := by
  rw [Kernel.snd_eq]
  exact HasCondDistrib.comp h measurable_snd

lemma HasLaw.prod_of_hasCondDistrib {Q : Measure 𝓨} [IsSFiniteKernel κ]
    (h1 : HasLaw X Q P) (h2 : HasCondDistrib Y X κ P) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (Q ⊗ₘ κ) P := by
  refine ⟨by fun_prop, ?_⟩
  rw [← compProd_map_condDistrib (by fun_prop), h1.map_eq]
  refine Measure.compProd_congr ?_
  rw [← h1.map_eq]
  exact h2.condDistrib_eq

lemma HasCondDistrib.comp_right [IsFiniteKernel κ] {f : 𝓩 → 𝓨}
    {hf : Measurable f} {Z : 𝓧 → 𝓩} (h : HasCondDistrib Y Z (κ.comap f hf) P) :
    HasCondDistrib Y (f ∘ Z) κ P := by
  have hY : AEMeasurable Y P := h.aemeasurable_fst
  have hZ : AEMeasurable Z P := h.aemeasurable_snd
  refine ⟨hY, hf.comp_aemeasurable hZ, ?_⟩
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ hY]
  calc P.map (fun a ↦ ((f ∘ Z) a, Y a))
  _ = (P.map (fun a ↦ (Z a, Y a))).map (Prod.map f id) := by
      rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) (hZ.prodMk hY)]
      rfl
  _ = (P.map Z ⊗ₘ κ.comap f hf).map (Prod.map f id) := by
      rw [(condDistrib_ae_eq_iff_measure_eq_compProd Z hY _).mp h.condDistrib_eq]
  _ = (P.map Z).map f ⊗ₘ κ := by
      ext s hs
      rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply (by measurability),
          Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
      rfl
  _ = P.map (f ∘ Z) ⊗ₘ κ := by
      rw [AEMeasurable.map_map_of_aemeasurable hf.aemeasurable hZ]

lemma HasCondDistrib.measurableEquiv_comp_right [IsFiniteKernel κ] (h : HasCondDistrib Y X κ P)
    (f : 𝓨 ≃ᵐ 𝓩) :
    HasCondDistrib Y (f ∘ X) (κ.comap f.symm (by fun_prop) : Kernel 𝓩 Ω) P := by
  apply HasCondDistrib.comp_right (hf := f.measurable)
  simpa [← Kernel.comap_comp_right]

lemma HasCondDistrib.of_compProd [IsFiniteKernel κ] {Z : 𝓧 → Ω'}
    {η : Kernel (𝓨 × Ω) Ω'} [IsMarkovKernel η]
    (h : HasCondDistrib (fun a ↦ (Y a, Z a)) X (κ ⊗ₖ η) P) :
    HasCondDistrib Z (fun a ↦ (X a, Y a)) η P := by
  have hZ : AEMeasurable Z P := h.aemeasurable_fst.snd
  have hX : AEMeasurable X P := h.aemeasurable_snd
  have hY : AEMeasurable Y P := h.aemeasurable_fst.fst
  refine ⟨hZ, (hX.prodMk hY), ?_⟩
  have hc := h.condDistrib_eq
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)] at hc ⊢
  calc P.map (fun a ↦ ((X a, Y a), Z a))
  _ = (P.map X ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm := by
      rw [← hc, AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
      rfl
  _ = P.map X ⊗ₘ κ ⊗ₘ η :=
      Measure.compProd_assoc
  _ = P.map (fun a ↦ (X a, Y a)) ⊗ₘ η := by
      rw [← (condDistrib_ae_eq_iff_measure_eq_compProd X hY κ).1]
      simpa using h.fst.condDistrib_eq

end ProbabilityTheory
