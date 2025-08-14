/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: EtienneMarion
-/
import Mathlib.Probability.Density
import Mathlib.Probability.Moments.Variance

/-!
# Law of a random variable

We introduce a predicate `HasLaw X μ P` stating that the random variable `X` has law `μ` under
the measure `P`. This is expressed as `P.map X = μ`. We also require `X` to be `P`-almost-everywhere
measurable. Indeed, if `X` is not almost-everywhere measurable then `P.map X` is defined to be `0`,
so that `HasLaw X 0 P` would be true. The measurability hypothesis ensures nice interactions with
operations on the codomain of `X`.
See for instance `HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`.
-/

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} (X : Ω → 𝓧)
  (μ : Measure 𝓧)

/-- The predicate `HasLaw X μ P` registers the fact that the random variable `X` has law `μ` under
the measure `P`, in other words that `P.map X = μ`. We also require `X` to be `AEMeasurable`,
to allow for nice interactions with operations on the codomain of `X`. See for instance
`HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`. -/
@[fun_prop]
structure HasLaw (P : Measure Ω := by volume_tac) : Prop where
  protected aemeasurable : AEMeasurable X P := by fun_prop
  protected map_eq : P.map X = μ

attribute [fun_prop] HasLaw.aemeasurable

variable {X μ} {P : Measure Ω}

lemma HasLaw.congr {Y : Ω → 𝓧} (hX : HasLaw X μ P) (hY : Y =ᵐ[P] X) : HasLaw Y μ P where
  aemeasurable := hX.aemeasurable.congr hY.symm
  map_eq := by rw [Measure.map_congr hY, hX.map_eq]

lemma _root_.MeasureTheory.MeasurePreserving.hasLaw (h : MeasurePreserving X P μ) :
    HasLaw X μ P where
  aemeasurable := h.measurable.aemeasurable
  map_eq := h.map_eq

lemma HasLaw.measurePreserving (h₁ : HasLaw X μ P) (h₂ : Measurable X) :
    MeasurePreserving X P μ where
  measurable := h₂
  map_eq := h₁.map_eq

@[fun_prop]
lemma HasLaw.comp {𝒴 : Type*} {m𝒴 : MeasurableSpace 𝒴} {ν : Measure 𝒴} {Y : 𝓧 → 𝒴}
    (hY : HasLaw Y ν μ) (hX : HasLaw X μ P) : HasLaw (Y ∘ X) ν P where
  aemeasurable := (hX.map_eq ▸ hY.aemeasurable).comp_aemeasurable hX.aemeasurable
  map_eq := by
    rw [← AEMeasurable.map_map_of_aemeasurable _ hX.aemeasurable, hX.map_eq, hY.map_eq]
    rw [hX.map_eq]; exact hY.aemeasurable

@[fun_prop]
lemma HasLaw.fun_comp {𝒴 : Type*} {m𝒴 : MeasurableSpace 𝒴} {ν : Measure 𝒴} {Y : 𝓧 → 𝒴}
    (hY : HasLaw Y ν μ) (hX : HasLaw X μ P) : HasLaw (fun ω ↦ Y (X ω)) ν P :=
  hY.comp hX

@[to_additive]
lemma IndepFun.hasLaw_mul {M : Type*} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
    {μ ν : Measure M} [SigmaFinite μ] [SigmaFinite ν] {X Y : Ω → M}
    (hX : HasLaw X μ P) (hY : HasLaw Y ν P) (hXY : IndepFun X Y P) :
    HasLaw (X * Y) (μ ∗ₘ ν) P where
  map_eq := by
    rw [hXY.map_mul_eq_map_mconv_map₀' hX.aemeasurable hY.aemeasurable, hX.map_eq, hY.map_eq]
    · rwa [hX.map_eq]
    · rwa [hY.map_eq]

@[to_additive]
lemma IndepFun.hasLaw_fun_mul {M : Type*} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
    {μ ν : Measure M} [SigmaFinite μ] [SigmaFinite ν] {X Y : Ω → M}
    (hX : HasLaw X μ P) (hY : HasLaw Y ν P) (hXY : IndepFun X Y P) :
    HasLaw (fun ω ↦ X ω * Y ω) (μ ∗ₘ ν) P := hXY.hasLaw_mul hX hY

lemma HasLaw.integral_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Ω → 𝓧} (hX : HasLaw X μ P) {f : 𝓧 → E} (hf : AEStronglyMeasurable f μ) :
    P[f ∘ X] = ∫ x, f x ∂μ := by
  rw [← hX.map_eq, integral_map hX.aemeasurable]
  · rfl
  · rwa [hX.map_eq]

lemma HasLaw.lintegral_comp {X : Ω → 𝓧} (hX : HasLaw X μ P) {f : 𝓧 → ℝ≥0∞}
    (hf : AEMeasurable f μ) : ∫⁻ ω, f (X ω) ∂P = ∫⁻ x, f x ∂μ := by
  rw [← hX.map_eq, lintegral_map' _ hX.aemeasurable]
  rwa [hX.map_eq]

lemma HasLaw.integral_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] {mE : MeasurableSpace E} [OpensMeasurableSpace E] {μ : Measure E}
    {X : Ω → E} (hX : HasLaw X μ P) : P[X] = ∫ x, x ∂μ := by
  rw [← Function.id_comp X, hX.integral_comp aestronglyMeasurable_id]
  simp

lemma HasLaw.covariance_comp (hX : HasLaw X μ P) {f g : 𝓧 → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    cov[f ∘ X, g ∘ X; P] = cov[f, g; μ] := by
  rw [← hX.map_eq, covariance_map]
  · rw [hX.map_eq]
    exact hf.aestronglyMeasurable
  · rw [hX.map_eq]
    exact hg.aestronglyMeasurable
  · exact hX.aemeasurable

lemma HasLaw.covariance_fun_comp (hX : HasLaw X μ P) {f g : 𝓧 → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    cov[fun ω ↦ f (X ω), fun ω ↦ g (X ω); P] = cov[f, g; μ] :=
  hX.covariance_comp hf hg

lemma HasLaw.variance_eq {μ : Measure ℝ} {X : Ω → ℝ} (hX : HasLaw X μ P) :
    Var[X; P] = Var[id; μ] := by
  rw [← hX.map_eq, variance_map aemeasurable_id hX.aemeasurable, Function.id_comp]

lemma HasPDF.hasLaw [h : HasPDF X P μ] : HasLaw X (μ.withDensity (pdf X P μ)) P where
  aemeasurable := h.aemeasurable
  map_eq := map_eq_withDensity_pdf X P μ

end ProbabilityTheory
