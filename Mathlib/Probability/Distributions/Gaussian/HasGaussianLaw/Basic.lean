/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.HasLaw

import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Gaussian random variables

In this file we define a predicate `HasGaussianLaw X P`, which states that under the probability
measure `P`, the random variable `X` has a Gaussian distribution, i.e. `IsGaussian (P.map X)`.

## Main definition

* `HasGaussianLaw X P`: The random variable `X` has a Gaussian distribution under the measure `P`.

## Tags

Gaussian random variable
-/

open MeasureTheory WithLp Complex Finset
open scoped ENNReal NNReal

variable {Ω ι E F : Type*} [Fintype ι] {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → E}

public section

namespace ProbabilityTheory

section Basic

variable [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [mE : MeasurableSpace E]

/-- The predicate `HasGaussianLaw X P` means that under the measure `P`,
`X` has a Gaussian distribution. -/
@[fun_prop]
structure HasGaussianLaw (X : Ω → E) (P : Measure Ω) : Prop where
  protected isGaussian_map : IsGaussian (P.map X)

lemma HasGaussianLaw.congr {Y : Ω → E} (hX : HasGaussianLaw X P) (h : ∀ᵐ ω ∂P, X ω = Y ω) :
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

variable
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  (L : E →L[ℝ] F)

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

lemma map (hX : HasGaussianLaw X P) : HasGaussianLaw (L ∘ X) P where
  isGaussian_map := by
    have := hX.isGaussian_map
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · infer_instance
    all_goals fun_prop (disch := assumption)

lemma map_fun (hX : HasGaussianLaw X P) : HasGaussianLaw (fun ω ↦ L (X ω)) P :=
  hX.map L

variable (L : E ≃L[ℝ] F)

lemma map_equiv (hX : HasGaussianLaw X P) : HasGaussianLaw (L ∘ X) P :=
  hX.map L.toContinuousLinearMap

lemma map_equiv_fun (hX : HasGaussianLaw X P) :
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

end Pi

end SpecificMaps

end HasGaussianLaw

end ProbabilityTheory
