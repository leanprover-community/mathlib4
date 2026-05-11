/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Density
public import Mathlib.Probability.Moments.Variance

/-!
# Law of a random variable

We introduce a predicate `HasLaw X μ P` stating that the random variable `X` has law `μ` under
the measure `P`. This is expressed as `P.map X = μ`. We also require `X` to be `P`-almost-everywhere
measurable. Indeed, if `X` is not almost-everywhere measurable then `P.map X` is defined to be `0`,
so that `HasLaw X 0 P` would be true. The measurability hypothesis ensures nice interactions with
operations on the codomain of `X`.
See for instance `HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`.
-/

public section

open MeasureTheory Measure

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {X Y : Ω → 𝓧}
  {μ : Measure 𝓧} {P : Measure Ω}

variable (X μ) in
/-- The predicate `HasLaw X μ P` registers the fact that the random variable `X` has law `μ` under
the measure `P`, in other words that `P.map X = μ`. We also require `X` to be `AEMeasurable`,
to allow for nice interactions with operations on the codomain of `X`. See for instance
`HasLaw.comp`, `IndepFun.hasLaw_mul` and `IndepFun.hasLaw_add`. -/
@[fun_prop]
structure HasLaw (P : Measure Ω := by volume_tac) : Prop where
  protected aemeasurable : AEMeasurable X P := by fun_prop
  protected map_eq : P.map X = μ

attribute [fun_prop] HasLaw.aemeasurable

lemma HasLaw.measure_eq (hX : HasLaw X μ P) {p : 𝓧 → Prop} (hp : MeasurableSet {x | p x}) :
    P {ω | p (X ω)} = μ {x | p x} := by
  rw [← hX.map_eq, map_apply_of_aemeasurable hX.aemeasurable hp]
  simp

lemma HasLaw.measureReal_eq (hX : HasLaw X μ P) {p : 𝓧 → Prop} (hp : MeasurableSet {x | p x}) :
    P.real {ω | p (X ω)} = μ.real {x | p x} := by
  rw [← hX.map_eq, map_measureReal_apply_of_aemeasurable hX.aemeasurable hp]
  simp

/-- If there is a random variable `X` with law `μ` such that `f(X)` has law `ν`, then
for any random variable `Y` with law `μ`, `f(Y)` has law `ν`. -/
lemma HasLaw.comp_of_hasLaw_comp {Ω' 𝓨 : Type*} {m' : MeasurableSpace Ω'} {m𝓨 : MeasurableSpace 𝓨}
    {P' : Measure Ω'} {ν : Measure 𝓨} {f : 𝓧 → 𝓨} {Y : Ω' → 𝓧} (hf : AEMeasurable f μ)
    (hX : HasLaw X μ P) (hY : HasLaw Y μ P') (h : HasLaw (fun ω ↦ f (X ω)) ν P) :
    HasLaw (fun ω ↦ f (Y ω)) ν P' where
  aemeasurable := (hY.map_eq ▸ hf).comp_aemeasurable hY.aemeasurable
  map_eq := by
    rw [← Function.comp_def,
      ← AEMeasurable.map_map_of_aemeasurable (hY.map_eq ▸ hf) hY.aemeasurable,
      hY.map_eq, ← hX.map_eq, AEMeasurable.map_map_of_aemeasurable (hX.map_eq ▸ hf) hX.aemeasurable,
      Function.comp_def, h.map_eq]

lemma HasLaw.congr (hX : HasLaw X μ P) (hY : Y =ᵐ[P] X) : HasLaw Y μ P where
  aemeasurable := hX.aemeasurable.congr hY.symm
  map_eq := by rw [map_congr hY, hX.map_eq]

lemma hasLaw_congr (hXY : X =ᵐ[P] Y) : HasLaw X μ P ↔ HasLaw Y μ P where
  mp h := h.congr hXY.symm
  mpr h := h.congr hXY

lemma _root_.MeasureTheory.MeasurePreserving.hasLaw (h : MeasurePreserving X P μ) :
    HasLaw X μ P where
  aemeasurable := h.measurable.aemeasurable
  map_eq := h.map_eq

lemma HasLaw.measurePreserving (h₁ : HasLaw X μ P) (h₂ : Measurable X) :
    MeasurePreserving X P μ where
  measurable := h₂
  map_eq := h₁.map_eq

protected lemma HasLaw.id : HasLaw id μ μ where
  map_eq := map_id

protected lemma HasLaw.ae_iff (hX : HasLaw X μ P) {p : 𝓧 → Prop} (hp : Measurable p) :
    (∀ᵐ ω ∂P, p (X ω)) ↔ ∀ᵐ x ∂μ, p x := by
  rw [← hX.map_eq, ae_map_iff hX.aemeasurable (measurableSet_setOf.2 hp)]

protected theorem HasLaw.isFiniteMeasure_iff (hX : HasLaw X μ P) :
    IsFiniteMeasure P ↔ IsFiniteMeasure μ := by
  rw [← hX.map_eq, isFiniteMeasure_map_iff hX.aemeasurable]

protected theorem HasLaw.isProbabilityMeasure_iff (hX : HasLaw X μ P) :
    IsProbabilityMeasure P ↔ IsProbabilityMeasure μ := by
  rw [← hX.map_eq, isProbabilityMeasure_map_iff hX.aemeasurable]

lemma HasLaw.isFiniteMeasure [IsFiniteMeasure μ] (hX : HasLaw X μ P) : IsFiniteMeasure P :=
  hX.isFiniteMeasure_iff.2 ‹_›

lemma HasLaw.isProbabilityMeasure [IsProbabilityMeasure μ] (hX : HasLaw X μ P) :
    IsProbabilityMeasure P := hX.isProbabilityMeasure_iff.2 ‹_›

@[fun_prop]
lemma HasLaw.comp {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {ν : Measure 𝓨} {Y : 𝓧 → 𝓨}
    (hY : HasLaw Y ν μ) (hX : HasLaw X μ P) : HasLaw (Y ∘ X) ν P where
  aemeasurable := (hX.map_eq ▸ hY.aemeasurable).comp_aemeasurable hX.aemeasurable
  map_eq := by
    rw [← AEMeasurable.map_map_of_aemeasurable _ hX.aemeasurable, hX.map_eq, hY.map_eq]
    rw [hX.map_eq]; exact hY.aemeasurable

@[fun_prop]
lemma HasLaw.fun_comp {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨} {ν : Measure 𝓨} {Y : 𝓧 → 𝓨}
    (hY : HasLaw Y ν μ) (hX : HasLaw X μ P) : HasLaw (fun ω ↦ Y (X ω)) ν P :=
  hY.comp hX

lemma _root_.MeasureTheory.MeasurePreserving.comp_hasLaw {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
    {ν : Measure 𝓨} {Y : 𝓧 → 𝓨} (hY : MeasurePreserving Y μ ν) (hX : HasLaw X μ P) :
    HasLaw (Y ∘ X) ν P :=
  hY.hasLaw.comp hX

lemma _root_.MeasureTheory.MeasurePreserving.fun_comp_hasLaw {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
    {ν : Measure 𝓨} {Y : 𝓧 → 𝓨} (hY : MeasurePreserving Y μ ν) (hX : HasLaw X μ P) :
    HasLaw (fun ω ↦ Y (X ω)) ν P :=
  hY.comp_hasLaw hX

@[to_additive]
lemma IndepFun.hasLaw_mul {M : Type*} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
    {μ ν : Measure M} [SigmaFinite μ] [SigmaFinite ν] {X Y : Ω → M}
    (hX : HasLaw X μ P) (hY : HasLaw Y ν P) (hXY : X ⟂ᵢ[P] Y) :
    HasLaw (X * Y) (μ ∗ₘ ν) P where
  map_eq := by
    rw [hXY.map_mul_eq_map_mconv_map₀' hX.aemeasurable hY.aemeasurable, hX.map_eq, hY.map_eq]
    · rwa [hX.map_eq]
    · rwa [hY.map_eq]

@[to_additive]
lemma IndepFun.hasLaw_fun_mul {M : Type*} [Monoid M] {mM : MeasurableSpace M} [MeasurableMul₂ M]
    {μ ν : Measure M} [SigmaFinite μ] [SigmaFinite ν] {X Y : Ω → M}
    (hX : HasLaw X μ P) (hY : HasLaw Y ν P) (hXY : X ⟂ᵢ[P] Y) :
    HasLaw (fun ω ↦ X ω * Y ω) (μ ∗ₘ ν) P := hXY.hasLaw_mul hX hY

lemma HasLaw.integral_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : Ω → 𝓧} (hX : HasLaw X μ P) {f : 𝓧 → E} (hf : AEStronglyMeasurable f μ) :
    P[f ∘ X] = ∫ x, f x ∂μ := by
  rw [← hX.map_eq, integral_map hX.aemeasurable, Function.comp_def]
  rwa [hX.map_eq]

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

lemma indepFun_iff_hasLaw_prodMk_prod [IsFiniteMeasure P] {𝓨 : Type*} {m𝓨 : MeasurableSpace 𝓨}
    {ν : Measure 𝓨} {Y : Ω → 𝓨} (hX : HasLaw X μ P) (hY : HasLaw Y ν P) :
    X ⟂ᵢ[P] Y ↔ HasLaw (fun ω ↦ (X ω, Y ω)) (μ.prod ν) P where
  mp h :=
    { map_eq := by
        rw [(indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).1 h, hX.map_eq,
          hY.map_eq] }
  mpr h := by
    rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
      h.map_eq, hX.map_eq, hY.map_eq]

alias ⟨IndepFun.hasLaw_prod, _⟩ := indepFun_iff_hasLaw_prodMk_prod

lemma iIndepFun.hasLaw_pi {ι : Type*} [Fintype ι] {𝓧 : ι → Type*} {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)}
    {μ : (i : ι) → Measure (𝓧 i)} {X : (i : ι) → Ω → 𝓧 i} (hX : ∀ i, HasLaw (X i) (μ i) P)
    (h : iIndepFun X P) :
    HasLaw (fun ω i ↦ X i ω) (Measure.pi μ) P where
  map_eq := by
    have := h.isProbabilityMeasure
    rw [(iIndepFun_iff_map_fun_eq_pi_map (by fun_prop)).1 h]
    simp_rw [fun i ↦ (hX i).map_eq]

lemma iIndepFun_iff_hasLaw_pi_pi [IsProbabilityMeasure P] {ι : Type*} [Fintype ι] {𝓧 : ι → Type*}
    {m𝓧 : ∀ i, MeasurableSpace (𝓧 i)} {μ : (i : ι) → Measure (𝓧 i)}
    {X : (i : ι) → Ω → 𝓧 i} (hX : ∀ i, HasLaw (X i) (μ i) P) :
    iIndepFun X P ↔ HasLaw (fun ω i ↦ X i ω) (Measure.pi μ) P where
  mp h := h.hasLaw_pi hX
  mpr h := by
    rw [iIndepFun_iff_map_fun_eq_pi_map (by fun_prop), h.map_eq]
    simp_rw [fun i ↦ (hX i).map_eq]

end ProbabilityTheory
