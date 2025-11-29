/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Basic
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

namespace ProbabilityTheory

variable {Ω E F ι : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω}

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
lemma HasGaussianLaw.aemeasurable (hX : HasGaussianLaw X P) : AEMeasurable X P := by
  by_contra! h
  have := hX.isGaussian_map
  rw [Measure.map_of_not_aemeasurable h] at this
  exact this.toIsProbabilityMeasure.ne_zero _ rfl

lemma HasGaussianLaw.isProbabilityMeasure (hX : HasGaussianLaw X P) : IsProbabilityMeasure P where
  measure_univ := by
    have := hX.isGaussian_map
    rw [← Set.preimage_univ (f := X), ← Measure.map_apply_of_aemeasurable hX.aemeasurable .univ,
      measure_univ]

variable {mE} in
lemma HasLaw.hasGaussianLaw {μ : Measure E} (hX : HasLaw X μ P) [IsGaussian μ] :
    HasGaussianLaw X P where
  isGaussian_map := by rwa [hX.map_eq]

end Basic

namespace HasGaussianLaw

variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] {X : Ω → E}

open scoped RealInnerProductSpace in
lemma charFun_map_eq [InnerProductSpace ℝ E] (t : E) (hX : HasGaussianLaw X P) :
    charFun (P.map X) t = exp ((P[fun ω ↦ ⟪t, X ω⟫] : ℝ) * I - Var[fun ω ↦ ⟪t, X ω⟫; P] / 2) := by
  rw [hX.isGaussian_map.charFun_eq, integral_map hX.aemeasurable (by fun_prop),
    variance_map (by fun_prop) hX.aemeasurable, integral_complex_ofReal]
  rfl

open scoped RealInnerProductSpace in
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

lemma map (hX : HasGaussianLaw X P) (L : E →L[ℝ] F) : HasGaussianLaw (L ∘ X) P where
  isGaussian_map := by
    have := hX.isGaussian_map
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · infer_instance
    all_goals fun_prop (disch := assumption)

lemma map_fun (hX : HasGaussianLaw X P) (L : E →L[ℝ] F) : HasGaussianLaw (fun ω ↦ L (X ω)) P :=
  hX.map L

lemma map_equiv (hX : HasGaussianLaw X P) (L : E ≃L[ℝ] F) : HasGaussianLaw (L ∘ X) P :=
  hX.map L.toContinuousLinearMap

lemma map_equiv_fun (hX : HasGaussianLaw X P) (L : E ≃L[ℝ] F) :
    HasGaussianLaw (fun ω ↦ L (X ω)) P := hX.map_equiv L

section SpecificMaps

lemma smul (c : ℝ) (hX : HasGaussianLaw X P) : HasGaussianLaw (c • X) P :=
  hX.map (.lsmul ℝ ℝ c)

lemma fun_smul (c : ℝ) (hX : HasGaussianLaw X P) :
    HasGaussianLaw (fun ω ↦ c • (X ω)) P :=
  hX.smul c

lemma neg (hX : HasGaussianLaw X P) : HasGaussianLaw (-X) P := by
  have : -X = (-1 : ℝ) • X := by simp
  rw [this]
  exact hX.smul _

lemma fun_neg (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω ↦ -(X ω)) P :=
  hX.neg

section Prod

variable [SecondCountableTopologyEither E F] {Y : Ω → F}

lemma toLp_prodMk (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ toLp p (X ω, Y ω)) P := by
  simp_rw [← WithLp.prodContinuousLinearEquiv_symm_apply p ℝ]
  exact hXY.map_equiv _

lemma fst (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw X P := by
  have : X = (ContinuousLinearMap.fst ℝ E F) ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  exact hXY.map _

lemma snd (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw Y P := by
  have : Y = (ContinuousLinearMap.snd ℝ E F) ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  exact hXY.map _

variable [SecondCountableTopology E] {Y : Ω → E}

lemma add (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (X + Y) P := by
  have : X + Y = (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) ∘
      (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  exact hXY.map _

lemma fun_add (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ X ω + Y ω) P :=
  hXY.add

lemma sub (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (X - Y) P := by
  have : X - Y = (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E) ∘
      (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  exact hXY.map _

lemma fun_sub (hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P) :
    HasGaussianLaw (fun ω ↦ X ω - Y ω) P :=
  hXY.sub

end Prod

section Pi

variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}

lemma eval (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (i : ι) :
    HasGaussianLaw (X i) P := by
  have : X i = (ContinuousLinearMap.proj (R := ℝ) (φ := E) i) ∘ (fun ω ↦ (X · ω)) := by ext; simp
  rw [this]
  exact hX.map _

lemma prodMk (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (i j : ι) :
    HasGaussianLaw (fun ω ↦ (X i ω, X j ω)) P := by
  have : (fun ω ↦ (X i ω, X j ω)) =
      ((ContinuousLinearMap.proj (R := ℝ) (φ := E) i).prod
      (ContinuousLinearMap.proj (R := ℝ) (φ := E) j)) ∘ (fun ω ↦ (X · ω)) := by ext <;> simp
  rw [this]
  exact hX.map _

lemma toLp_pi (p : ℝ≥0∞) [Fact (1 ≤ p)] (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) :
    HasGaussianLaw (fun ω ↦ toLp p (X · ω)) P := by
  simp_rw [← PiLp.continuousLinearEquiv_symm_apply p ℝ]
  exact hX.map_equiv _

lemma sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {X : ι → Ω → E} (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) :
    HasGaussianLaw (∑ i, X i) P := by
  have : ∑ i, X i = ⇑(∑ i, ContinuousLinearMap.proj (R := ℝ) i) ∘ (fun ω ↦ (X · ω)) := by
    ext; simp
  rw [this]
  exact hX.map _

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
