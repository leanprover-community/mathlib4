/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Strongly measurable and finitely strongly measurable functions

This file contains some further development of strongly measurable and finitely strongly measurable
functions, started in `Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean`.

## References

* [Hytönen, Tuomas, Jan Van Neerven, Mark Veraar, and Lutz Weis. Analysis in Banach spaces.
  Springer, 2016.][Hytonen_VanNeerven_Veraar_Wies_2016]

-/

open MeasureTheory Filter Set ENNReal NNReal

variable {α β γ : Type*} {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace β]
  [TopologicalSpace γ] {f g : α → β}

@[fun_prop]
lemma aestronglyMeasurable_dirac [MeasurableSingletonClass α] {a : α} {f : α → β} :
    AEStronglyMeasurable f (Measure.dirac a) :=
  ⟨fun _ ↦ f a, stronglyMeasurable_const, ae_eq_dirac f⟩

theorem MeasureTheory.AEStronglyMeasurable.comp_measurePreserving
    {γ : Type*} {_ : MeasurableSpace γ} {_ : MeasurableSpace α} {f : γ → α} {μ : Measure γ}
    {ν : Measure α} (hg : AEStronglyMeasurable g ν) (hf : MeasurePreserving f μ ν) :
    AEStronglyMeasurable (g ∘ f) μ :=
  hg.comp_quasiMeasurePreserving hf.quasiMeasurePreserving

theorem MeasureTheory.MeasurePreserving.aestronglyMeasurable_comp_iff {β : Type*}
    {f : α → β} {mα : MeasurableSpace α} {μa : Measure α} {mβ : MeasurableSpace β} {μb : Measure β}
    (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) {g : β → γ} :
    AEStronglyMeasurable (g ∘ f) μa ↔ AEStronglyMeasurable g μb := by
  rw [← hf.map_eq, h₂.aestronglyMeasurable_map_iff]

section NormedSpace

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem aestronglyMeasurable_smul_const_iff {f : α → 𝕜} {c : E} (hc : c ≠ 0) :
    AEStronglyMeasurable (fun x => f x • c) μ ↔ AEStronglyMeasurable f μ :=
  (isClosedEmbedding_smul_left hc).isEmbedding.aestronglyMeasurable_comp_iff

end NormedSpace

section ContinuousLinearMapNontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

theorem StronglyMeasurable.apply_continuousLinearMap
    {_m : MeasurableSpace α} {φ : α → F →L[𝕜] E} (hφ : StronglyMeasurable φ) (v : F) :
    StronglyMeasurable fun a => φ a v :=
  (ContinuousLinearMap.apply 𝕜 E v).continuous.comp_stronglyMeasurable hφ

@[measurability]
theorem MeasureTheory.AEStronglyMeasurable.apply_continuousLinearMap {φ : α → F →L[𝕜] E}
    (hφ : AEStronglyMeasurable φ μ) (v : F) :
    AEStronglyMeasurable (fun a => φ a v) μ :=
  (ContinuousLinearMap.apply 𝕜 E v).continuous.comp_aestronglyMeasurable hφ

theorem ContinuousLinearMap.aestronglyMeasurable_comp₂ (L : E →L[𝕜] F →L[𝕜] G) {f : α → E}
    {g : α → F} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => L (f x) (g x)) μ :=
  L.continuous₂.comp_aestronglyMeasurable₂ hf hg

end ContinuousLinearMapNontriviallyNormedField

theorem aestronglyMeasurable_withDensity_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : α → ℝ≥0} (hf : Measurable f) {g : α → E} :
    AEStronglyMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEStronglyMeasurable (fun x => (f x : ℝ) • g x) μ := by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x ≠ 0 } := (hf (measurableSet_singleton 0)).compl
    refine ⟨fun x => (f x : ℝ) • g' x, hf.coe_nnreal_real.stronglyMeasurable.smul g'meas, ?_⟩
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ { x | f x ≠ 0 }
    · rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg'] with a ha h'a
      have : (f a : ℝ≥0∞) ≠ 0 := by simpa only [Ne, ENNReal.coe_eq_zero] using h'a
      rw [ha this]
    · filter_upwards [ae_restrict_mem A.compl] with x hx
      simp only [Classical.not_not, mem_setOf_eq, mem_compl_iff] at hx
      simp [hx]
  · rintro ⟨g', g'meas, hg'⟩
    refine ⟨fun x => (f x : ℝ)⁻¹ • g' x, hf.coe_nnreal_real.inv.stronglyMeasurable.smul g'meas, ?_⟩
    rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg'] with x hx h'x
    rw [← hx, smul_smul, inv_mul_cancel₀, one_smul]
    simp only [Ne, ENNReal.coe_eq_zero] at h'x
    simpa only [NNReal.coe_eq_zero, Ne] using h'x
