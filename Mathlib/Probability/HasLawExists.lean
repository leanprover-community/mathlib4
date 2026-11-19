/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Probability.Independence.InfinitePi

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Existence of Random Variables

This file contains lemmas that state the existence of random variables with given distributions
and a given dependency structure (currently only mutual independence is considered).
-/

public section

open MeasureTheory Measure

namespace ProbabilityTheory

universe u v

lemma _root_.MeasureTheory.Measure.exists_hasLaw {𝓧 : Type u} {m𝓧 : MeasurableSpace 𝓧}
    (μ : Measure 𝓧) :
    ∃ Ω : Type u, ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : Ω → 𝓧,
      Measurable X ∧ HasLaw X μ P :=
  ⟨𝓧, m𝓧, μ, id, measurable_id, .id⟩

lemma exists_hasLaw_indepFun {𝓧 : Type u} {𝓨 : Type v}
    {m𝓧 : MeasurableSpace 𝓧} (μ : Measure 𝓧) [IsProbabilityMeasure μ]
    {m𝓨 : MeasurableSpace 𝓨} (ν : Measure 𝓨) [IsProbabilityMeasure ν] :
    ∃ Ω : Type (max u v), ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : Ω → 𝓧,
      ∃ Y : Ω → 𝓨, (Measurable X) ∧ (Measurable Y) ∧ (HasLaw X μ P) ∧ (HasLaw Y ν P) ∧ X ⟂ᵢ[P] Y ∧
      IsProbabilityMeasure P := by
  refine ⟨𝓧 × 𝓨, inferInstance, μ.prod ν, Prod.fst, Prod.snd, measurable_fst, measurable_snd,
    measurePreserving_fst.hasLaw, measurePreserving_snd.hasLaw,
    indepFun_prod measurable_id measurable_id, inferInstance⟩

lemma exists_hasLaw_iIndepFun {ι : Type v} (𝓧 : ι → Type u)
    {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} (μ : (i : ι) → Measure (𝓧 i))
    [hμ : ∀ i, IsProbabilityMeasure (μ i)] :
    ∃ Ω : Type (max u v), ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : (i : ι) → Ω → (𝓧 i),
      (∀ i, Measurable (X i)) ∧ (∀ i, HasLaw (X i) (μ i) P)
        ∧ iIndepFun X P ∧ IsProbabilityMeasure P := by
  use Π i, (𝓧 i), .pi, infinitePi μ, fun i ↦ Function.eval i
  refine ⟨by fun_prop, fun i ↦ MeasurePreserving.hasLaw (measurePreserving_eval_infinitePi _ _),
    ?_, inferInstance⟩
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop), map_id']
  congr
  funext i
  exact ((measurePreserving_eval_infinitePi μ i).map_eq).symm

lemma exists_iid (ι : Type v) {𝓧 : Type u} {m𝓧 : MeasurableSpace 𝓧}
    (μ : Measure 𝓧) [IsProbabilityMeasure μ] :
    ∃ Ω : Type (max u v), ∃ _ : MeasurableSpace Ω, ∃ P : Measure Ω, ∃ X : ι → Ω → 𝓧,
      (∀ i, Measurable (X i)) ∧ (∀ i, HasLaw (X i) μ P) ∧ iIndepFun X P ∧ IsProbabilityMeasure P :=
  exists_hasLaw_iIndepFun (fun _ ↦ 𝓧) (fun _ ↦ μ)

end ProbabilityTheory
