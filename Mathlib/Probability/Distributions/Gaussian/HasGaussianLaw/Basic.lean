/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def
public import Mathlib.Probability.HasLaw

import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian random variables

In this file we prove basic properties of Gaussian random variables.

# Implementation note

Many lemmas are duplicated with an expanded form of some function. For instance there is
`HasGaussianLaw.add` and `HasGaussianLaw.fun_add`. The reason is that if someone wants for instance
to rewrite using `HasGaussianLaw.charFunDual_map_eq` and provide the proof of `HasGaussianLaw`
directly through dot notation, the lemma used must syntactically correspond to the random variable.

## Tags

Gaussian random variable
-/

public section

open MeasureTheory ENNReal WithLp Complex
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {Ω E F ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

section Basic

variable [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [mE : MeasurableSpace E]
  {X Y : Ω → E}

lemma HasGaussianLaw.congr {Y : Ω → E} (hX : HasGaussianLaw X P) (h : X =ᵐ[P] Y) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    rw [← Measure.map_congr h]
    exact hX.isGaussian_map

lemma IsGaussian.hasGaussianLaw [IsGaussian (P.map X)] : HasGaussianLaw X P where
  isGaussian_map := inferInstance

variable {mE} in
lemma IsGaussian.hasGaussianLaw_id {μ : Measure E} [IsGaussian μ] : HasGaussianLaw id μ where
  isGaussian_map := by rwa [Measure.map_id]

@[fun_prop, measurability]
lemma HasGaussianLaw.aemeasurable (hX : HasGaussianLaw X P) : AEMeasurable X P :=
  AEMeasurable.of_map_ne_zero hX.isGaussian_map.toIsProbabilityMeasure.ne_zero

lemma HasGaussianLaw.isProbabilityMeasure (hX : HasGaussianLaw X P) : IsProbabilityMeasure P :=
    haveI := hX.isGaussian_map
    P.isProbabilityMeasure_of_map X

variable {mE} in
lemma HasLaw.hasGaussianLaw {μ : Measure E} (hX : HasLaw X μ P) [IsGaussian μ] :
    HasGaussianLaw X P where
  isGaussian_map := by rwa [hX.map_eq]

lemma HasGaussianLaw.map_of_measurable {F : Type*} [TopologicalSpace F] [AddCommMonoid F]
    [Module ℝ F] [MeasurableSpace F] [OpensMeasurableSpace F]
    (L : E →L[ℝ] F) (hX : HasGaussianLaw X P) (hL : Measurable L) :
    HasGaussianLaw (L ∘ X) P where
  isGaussian_map := by
    have := hX.isGaussian_map
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · exact isGaussian_map_of_measurable hL
    all_goals fun_prop

end Basic

namespace HasGaussianLaw

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {X : Ω → E}

lemma charFun_map_eq [InnerProductSpace ℝ E] (t : E) (hX : HasGaussianLaw X P) :
    charFun (P.map X) t = exp ((P[fun ω ↦ ⟪t, X ω⟫] : ℝ) * I - Var[fun ω ↦ ⟪t, X ω⟫; P] / 2) := by
  rw [hX.isGaussian_map.charFun_eq, integral_map hX.aemeasurable (by fun_prop),
    variance_map (by fun_prop) hX.aemeasurable, integral_complex_ofReal]
  rfl

lemma _root_.ProbabilityTheory.hasGaussianLaw_iff_charFun_map_eq [CompleteSpace E]
    [InnerProductSpace ℝ E] [IsFiniteMeasure P] (hX : AEMeasurable X P) :
    HasGaussianLaw X P ↔ ∀ t,
    charFun (P.map X) t = exp ((P[fun ω ↦ ⟪t, X ω⟫] : ℝ) * I - Var[fun ω ↦ ⟪t, X ω⟫; P] / 2) where
  mp h := h.charFun_map_eq
  mpr h := by
    refine ⟨isGaussian_iff_charFun_eq.2 fun t ↦ ?_⟩
    rw [h, integral_map, variance_map, integral_complex_ofReal]
    · rfl
    all_goals fun_prop

variable [NormedSpace ℝ E]

lemma charFunDual_map_eq (L : StrongDual ℝ E) (hX : HasGaussianLaw X P) :
    charFunDual (P.map X) L = exp ((P[L ∘ X] : ℝ) * I - Var[L ∘ X; P] / 2) := by
  rw [hX.isGaussian_map.charFunDual_eq, integral_map hX.aemeasurable (by fun_prop),
    variance_map (by fun_prop) hX.aemeasurable, integral_complex_ofReal]
  rfl

lemma _root_.ProbabilityTheory.hasGaussianLaw_iff_charFunDual_map_eq
    [IsFiniteMeasure P] (hX : AEMeasurable X P) :
    HasGaussianLaw X P ↔ ∀ L,
    charFunDual (P.map X) L = exp ((P[L ∘ X] : ℝ) * I - Var[L ∘ X; P] / 2) where
  mp h := h.charFunDual_map_eq
  mpr h := by
    refine ⟨isGaussian_iff_charFunDual_eq.2 fun t ↦ ?_⟩
    rw [h, integral_map, variance_map, integral_complex_ofReal]
    · rfl
    all_goals fun_prop

lemma charFunDual_map_eq_fun (L : StrongDual ℝ E) (hX : HasGaussianLaw X P) :
    charFunDual (P.map X) L = exp ((∫ ω, L (X ω) ∂P) * I - Var[fun ω ↦ L (X ω); P] / 2) := by
  rw [hX.charFunDual_map_eq]
  rfl

/-- A Gaussian random variable has moments of all orders. -/
lemma memLp [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P)
    {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp X p P := by
  rw [← Function.id_comp X, ← memLp_map_measure_iff]
  · exact hX.isGaussian_map.memLp_id _ p hp
  all_goals fun_prop

lemma memLp_two [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P) :
    MemLp X 2 P := hX.memLp (by norm_num)

lemma integrable [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P) :
    Integrable X P :=
  memLp_one_iff_integrable.1 <| hX.memLp (by norm_num)

variable [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma map (hX : HasGaussianLaw X P) (L : E →L[ℝ] F) : HasGaussianLaw (L ∘ X) P :=
    hX.map_of_measurable L (by fun_prop)

lemma map_fun (hX : HasGaussianLaw X P) (L : E →L[ℝ] F) : HasGaussianLaw (fun ω ↦ L (X ω)) P :=
  hX.map L

lemma map_equiv (hX : HasGaussianLaw X P) (L : E ≃L[ℝ] F) : HasGaussianLaw (L ∘ X) P :=
  hX.map L.toContinuousLinearMap

lemma map_equiv_fun (hX : HasGaussianLaw X P) (L : E ≃L[ℝ] F) :
    HasGaussianLaw (fun ω ↦ L (X ω)) P := hX.map_equiv L

section SpecificMaps

lemma smul (c : ℝ) (hX : HasGaussianLaw X P) : HasGaussianLaw (c • X) P :=
  hX.map (.lsmul ℝ ℝ c)

lemma fun_smul (c : ℝ) (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω ↦ c • (X ω)) P :=
  hX.smul c

lemma neg (hX : HasGaussianLaw X P) : HasGaussianLaw (-X) P := by simpa using hX.smul (-1)

lemma fun_neg (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω ↦ -(X ω)) P :=
  hX.neg

section Prod

variable {Y : Ω → F}

lemma toLp_prodMk [SecondCountableTopologyEither E F] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ toLp p (X ω, Y ω)) P :=
  hXY.map_equiv (WithLp.prodContinuousLinearEquiv p ℝ E F).symm

omit [BorelSpace F] in
lemma fst (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw X P :=
  hXY.map_of_measurable (.fst ℝ E F) measurable_fst

omit [BorelSpace E] in
lemma snd (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw Y P :=
  hXY.map_of_measurable (.snd ℝ E F) measurable_snd

variable [SecondCountableTopology E] {Y : Ω → E}

lemma add (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw (X + Y) P :=
  hXY.map (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E)

lemma fun_add (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ X ω + Y ω) P :=
  hXY.add

lemma sub (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) : HasGaussianLaw (X - Y) P :=
  hXY.map (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E)

lemma fun_sub (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ X ω - Y ω) P :=
  hXY.sub

end Prod

section Pi

variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  {X : (i : ι) → Ω → E i}

lemma eval (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (i : ι) :
    HasGaussianLaw (X i) P := hX.map_of_measurable (.proj i) (measurable_pi_apply i)

variable [∀ i, SecondCountableTopology (E i)]

lemma prodMk [Finite ι] (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (i j : ι) :
    HasGaussianLaw (fun ω ↦ (X i ω, X j ω)) P :=
    letI := Fintype.ofFinite ι
    hX.map (.prod (.proj i) (.proj j))

variable [Fintype ι]

lemma toLp_pi (p : ℝ≥0∞) [Fact (1 ≤ p)] (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) :
    HasGaussianLaw (fun ω ↦ toLp p (X · ω)) P :=
  hX.map_equiv (PiLp.continuousLinearEquiv p ℝ E).symm

lemma sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {X : ι → Ω → E} (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) :
    HasGaussianLaw (∑ i, X i) P := by
  convert hX.map (∑ i, .proj i)
  ext; simp

lemma fun_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {X : ι → Ω → E} (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) :
    HasGaussianLaw (fun ω ↦ ∑ i, X i ω) P := by
  convert hX.sum
  simp

end Pi

end SpecificMaps

end HasGaussianLaw

end ProbabilityTheory
