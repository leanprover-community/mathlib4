/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.HasLaw

@[expose] public section


open MeasureTheory ENNReal WithLp

namespace ProbabilityTheory

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → E}

section Basic

variable [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E] [mE : MeasurableSpace E]

/-- The predicate `HasGaussianLaw X P` means that under the measure `P`,
`X` has a Gaussian distribution. -/
class HasGaussianLaw (X : Ω → E) (P : Measure Ω) :
    Prop where
  protected isGaussian_map : IsGaussian (P.map X)

attribute [instance] HasGaussianLaw.isGaussian_map

lemma HasGaussianLaw.congr {Y : Ω → E} [HasGaussianLaw X P] (h : ∀ᵐ ω ∂P, X ω = Y ω) :
    HasGaussianLaw Y P where
  isGaussian_map := by
    rw [← Measure.map_congr h]
    infer_instance

instance IsGaussian.hasGaussianLaw [IsGaussian (P.map X)] :
    HasGaussianLaw X P where
  isGaussian_map := inferInstance

variable {mE} in
instance IsGaussian.hasGaussianLaw_id {μ : Measure E} [IsGaussian μ] :
    HasGaussianLaw id μ where
  isGaussian_map := by rwa [Measure.map_id]

@[fun_prop, measurability]
lemma HasGaussianLaw.aemeasurable [hX : HasGaussianLaw X P] : AEMeasurable X P := by
  by_contra! h
  have := hX.isGaussian_map
  rw [Measure.map_of_not_aemeasurable h] at this
  exact this.toIsProbabilityMeasure.ne_zero _ rfl

lemma HasGaussianLaw.isProbabilityMeasure [HasGaussianLaw X P] : IsProbabilityMeasure P where
  measure_univ := by
    rw [← Set.preimage_univ (f := X), ← Measure.map_apply_of_aemeasurable (by fun_prop) .univ,
      measure_univ]

variable {mE} in
lemma HasLaw.hasGaussianLaw {μ : Measure E} (hX : HasLaw X μ P) [IsGaussian μ] :
    HasGaussianLaw X P where
  isGaussian_map := by rwa [hX.map_eq]

end Basic

section NormedSpace

variable
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  (L : E →L[ℝ] F)

instance HasGaussianLaw.map [HasGaussianLaw X P] : HasGaussianLaw (L ∘ X) P where
  isGaussian_map := by
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · infer_instance
    all_goals fun_prop

instance HasGaussianLaw.map_fun [hX : HasGaussianLaw X P] : HasGaussianLaw (fun ω ↦ L (X ω)) P :=
  hX.map L

variable (L : E ≃L[ℝ] F)

instance HasGaussianLaw.map_equiv [HasGaussianLaw X P] : HasGaussianLaw (L ∘ X) P where
  isGaussian_map := by
    rw [← AEMeasurable.map_map_of_aemeasurable]
    · infer_instance
    all_goals fun_prop

instance HasGaussianLaw.map_equiv_fun [hX : HasGaussianLaw X P] :
    HasGaussianLaw (fun ω ↦ L (X ω)) P := hX.map_equiv L

section SpecificMaps

instance HasGaussianLaw.smul (c : ℝ) [hX : HasGaussianLaw X P] : HasGaussianLaw (c • X) P :=
  hX.map (.lsmul ℝ ℝ c)

instance HasGaussianLaw.fun_smul (c : ℝ) [hX : HasGaussianLaw X P] :
    HasGaussianLaw (fun ω ↦ c • (X ω)) P :=
  hX.smul c

instance HasGaussianLaw.neg [hX : HasGaussianLaw X P] : HasGaussianLaw (-X) P := by
  have : -X = (-1 : ℝ) • X := by simp
  rw [this]
  infer_instance

instance HasGaussianLaw.fun_neg [hX : HasGaussianLaw X P] : HasGaussianLaw (fun ω ↦ -(X ω)) P :=
  hX.neg

section Prod

variable [SecondCountableTopologyEither E F] {Y : Ω → F}

instance HasGaussianLaw.toLp_prodMk (p : ℝ≥0∞) [Fact (1 ≤ p)]
    [HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw (fun ω ↦ toLp p (X ω, Y ω)) P := by
  simp_rw [← WithLp.prodContinuousLinearEquiv_symm_apply p ℝ]
  infer_instance

lemma HasGaussianLaw.fst [HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw X P := by
  have : X = (ContinuousLinearMap.fst ℝ E F) ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  infer_instance

lemma HasGaussianLaw.snd [HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw Y P := by
  have : Y = (ContinuousLinearMap.snd ℝ E F) ∘ (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  infer_instance

variable [SecondCountableTopology E] {Y : Ω → E}

instance HasGaussianLaw.add [hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw (X + Y) P := by
  have : X + Y = (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E) ∘
      (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  infer_instance

instance HasGaussianLaw.fun_add [hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw (fun ω ↦ X ω + Y ω) P :=
  hXY.add

instance HasGaussianLaw.sub [hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw (X - Y) P := by
  have : X - Y = (ContinuousLinearMap.fst ℝ E E - ContinuousLinearMap.snd ℝ E E) ∘
      (fun ω ↦ (X ω, Y ω)) := by ext; simp
  rw [this]
  infer_instance

instance HasGaussianLaw.fun_sub [hXY : HasGaussianLaw (fun ω ↦ (X ω, Y ω)) P] :
    HasGaussianLaw (fun ω ↦ X ω - Y ω) P :=
  hXY.sub

end Prod

section Pi

variable {ι : Type*} [Fintype ι]

section Dependent

variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}

instance HasGaussianLaw.eval [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}
    [h : HasGaussianLaw (fun ω ↦ (X · ω)) P] (i : ι) :
    HasGaussianLaw (X i) P := by
  have : X i = (ContinuousLinearMap.proj (R := ℝ) (φ := E) i) ∘ (fun ω ↦ (X · ω)) := by ext; simp
  rw [this]
  infer_instance

instance HasGaussianLaw.prodMk [∀ i, SecondCountableTopology (E i)] {X : (i : ι) → Ω → E i}
    [h : HasGaussianLaw (fun ω ↦ (X · ω)) P] (i j : ι) :
    HasGaussianLaw (fun ω ↦ (X i ω, X j ω)) P := by
  have : (fun ω ↦ (X i ω, X j ω)) =
      ((ContinuousLinearMap.proj (R := ℝ) (φ := E) i).prod
      (ContinuousLinearMap.proj (R := ℝ) (φ := E) j)) ∘ (fun ω ↦ (X · ω)) := by ext <;> simp
  rw [this]
  infer_instance

instance HasGaussianLaw.sub' [h : HasGaussianLaw (fun ω ↦ (X · ω)) P] (i j : ι) :
    HasGaussianLaw (X i - X j) P := by
  have : X i - X j = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ E) i -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ E) j) ∘ (fun ω ↦ (X · ω)) := by ext; simp
  rw [this]
  infer_instance

instance HasGaussianLaw.toLp_comp_pi (p : ℝ≥0∞) [Fact (1 ≤ p)]
    [HasGaussianLaw (fun ω ↦ (X · ω)) P] :
    HasGaussianLaw (fun ω ↦ toLp p (X · ω)) P := by
  rw [← PiLp.continuousLinearEquiv_symm_apply p ℝ]
  infer_instance

instance IsGaussian.hasGaussianLaw_eval {μ : Measure (Π i, E i)} [IsGaussian μ] (i : ι) :
    HasGaussianLaw (fun x ↦ x i) μ :=
  HasGaussianLaw.eval (h := IsGaussian.hasGaussianLaw_id) i

instance IsGaussian.hasGaussianLaw_eval_piLp (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {μ : Measure (PiLp p E)} [IsGaussian μ] (i : ι) : HasGaussianLaw (fun x ↦ x i) μ :=
  HasGaussianLaw.eval
    (h := IsGaussian.hasGaussianLaw_id.map_equiv (PiLp.continuousLinearEquiv p ℝ E)) i

end Dependent

section Nondependent

variable [SecondCountableTopology E] {X : ι → Ω → E}

instance HasGaussianLaw.sub' [h : HasGaussianLaw (fun ω ↦ (X · ω)) P] (i j : ι) :
    HasGaussianLaw (X i - X j) P := inferInstance

instance IsGaussian.hasGaussianLaw_sub_eval {μ : Measure (ι → E)} [IsGaussian μ] (i j : ι) :
    HasGaussianLaw (fun x ↦ x i - x j) μ :=
  HasGaussianLaw.sub (h := IsGaussian.hasGaussianLaw_id) i j

instance IsGaussian.hasGaussianLaw_sub_eval_piLp (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {μ : Measure (PiLp p (fun _ ↦ E))} [IsGaussian μ] (i j : ι) :
    HasGaussianLaw (fun x ↦ x i - x j) μ :=
  HasGaussianLaw.sub
    (h := IsGaussian.hasGaussianLaw_id.map_equiv (PiLp.continuousLinearEquiv p ℝ (fun _ : ι ↦ E)))
    i j

end Nondependent

end Pi

end SpecificMaps

end NormedSpace

end HasGaussianLaw

end ProbabilityTheory
