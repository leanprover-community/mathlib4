/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Independence.Basic

open Complex MeasureTheory Measure

open scoped ENNReal RealInnerProductSpace

namespace ProbabilityTheory

section InnerProductSpace

section Prod

variable {E F Ω : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [InnerProductSpace ℝ E]
  [InnerProductSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E} {Y : Ω → F}
  (t : WithLp 2 (E × F))

lemma IndepFun.charFun_eq_mul (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) (h : IndepFun X Y μ) :
    charFun (μ.map fun ω ↦ (WithLp.equiv 2 _).symm (X ω, Y ω)) t =
      charFun (μ.map X) (WithLp.equiv 2 (E × F) t).1 *
      charFun (μ.map Y) (WithLp.equiv 2 (E × F) t).2 := by
  change charFun (μ.map (_ ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable,
    (indepFun_iff_map_prod_eq_prod_map_map mX mY).1 h, charFun_prod]
  all_goals fun_prop

lemma indepFun_iff_charFun_eq_mul [CompleteSpace E] [CompleteSpace F] [BorelSpace E] [BorelSpace F]
    [SecondCountableTopology E] [SecondCountableTopology F]
    (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) :
    IndepFun X Y μ ↔ ∀ t,
      charFun (μ.map fun ω ↦ (WithLp.equiv 2 _).symm (X ω, Y ω)) t =
      charFun (μ.map X) (WithLp.equiv 2 (E × F) t).1 *
      charFun (μ.map Y) (WithLp.equiv 2 (E × F) t).2 := by
  change _ ↔ ∀ _, charFun (μ.map (_ ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable, charFun_eq_prod_iff,
    indepFun_iff_map_prod_eq_prod_map_map mX mY]
  all_goals fun_prop

end Prod

section Pi

variable {ι Ω : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Π i, Ω → (E i)}
  (t : PiLp 2 E)

lemma iIndepFun.charFun_eq_pi (mX : ∀ i, AEMeasurable (X i) μ) (h : iIndepFun X μ) :
    charFun (μ.map fun ω ↦ (WithLp.equiv 2 _).symm fun i ↦ X i ω) t =
    ∏ i, charFun (μ.map (X i)) (t i) := by
  change charFun (μ.map (_ ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable, (iIndepFun_iff_map_fun_eq_pi_map mX).1 h, charFun_pi]
  all_goals fun_prop

lemma iIndepFun_iff_charFun_eq_pi [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] (mX : ∀ i, AEMeasurable (X i) μ) :
    iIndepFun X μ ↔ ∀ t,
      charFun (μ.map fun ω ↦ (WithLp.equiv 2 _).symm fun i ↦ X i ω) t =
      ∏ i, charFun (μ.map (X i)) (t i) := by
  change _ ↔ ∀ _, charFun (μ.map (_ ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable, charFun_eq_pi_iff,
    iIndepFun_iff_map_fun_eq_pi_map mX]
  all_goals fun_prop

end Pi

end InnerProductSpace

section NormedSpace

section Prod

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] {E F Ω : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → E} {Y : Ω → F}

lemma IndepFun.charFunDual_eq_mul (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ)
    (h : IndepFun X Y μ) (L : NormedSpace.Dual ℝ (E × F)) :
    charFunDual (μ.map fun ω ↦ (X ω, Y ω)) L =
      charFunDual (μ.map X) (L.comp (.inl ℝ E F)) *
      charFunDual (μ.map Y) (L.comp (.inr ℝ E F)) := by
  rw [(indepFun_iff_map_prod_eq_prod_map_map mX mY).1 h, charFunDual_prod]

lemma IndepFun.charFunDual_eq_mul' (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ)
    (h : IndepFun X Y μ) (L : NormedSpace.Dual ℝ (WithLp p (E × F))) :
    charFunDual (μ.map fun ω ↦ (WithLp.equiv p (E × F)).symm (X ω, Y ω)) L =
      charFunDual (μ.map X) (L.comp
        ((WithLp.prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inl ℝ E F))) *
      charFunDual (μ.map Y) (L.comp
        ((WithLp.prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inr ℝ E F))) := by
  change charFunDual (μ.map (_ ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable,
    (indepFun_iff_map_prod_eq_prod_map_map mX mY).1 h, charFunDual_prod']
  all_goals fun_prop

lemma indepFun_iff_charFunDual_eq_mul [CompleteSpace E] [CompleteSpace F] [BorelSpace E]
    [BorelSpace F] [SecondCountableTopology E] [SecondCountableTopology F]
    (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) :
    IndepFun X Y μ ↔ ∀ L,
      charFunDual (μ.map fun ω ↦ (X ω, Y ω)) L =
      charFunDual (μ.map X) (L.comp (.inl ℝ E F)) *
      charFunDual (μ.map Y) (L.comp (.inr ℝ E F)) := by
  rw [charFunDual_eq_prod_iff, indepFun_iff_map_prod_eq_prod_map_map mX mY]

lemma indepFun_iff_charFunDual_eq_mul' [CompleteSpace E] [CompleteSpace F] [BorelSpace E]
    [BorelSpace F] [SecondCountableTopology E] [SecondCountableTopology F]
    (mX : AEMeasurable X μ) (mY : AEMeasurable Y μ) :
    IndepFun X Y μ ↔ ∀ L,
      charFunDual (μ.map fun ω ↦ (WithLp.equiv p (E × F)).symm (X ω, Y ω)) L =
      charFunDual (μ.map X) (L.comp
        ((WithLp.prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inl ℝ E F))) *
      charFunDual (μ.map Y) (L.comp
        ((WithLp.prodContinuousLinearEquiv p ℝ E F).symm.toContinuousLinearMap.comp
          (.inr ℝ E F))) := by
  change _ ↔ ∀ _, charFunDual (μ.map (_ ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable, charFunDual_eq_prod_iff',
    indepFun_iff_map_prod_eq_prod_map_map mX mY]
  all_goals fun_prop

end Prod

section Pi

variable (p : ℝ≥0∞) [Fact (1 ≤ p)] {ι Ω : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Π i, Ω → (E i)}

lemma iIndepFun.charFunDual_eq_pi (mX : ∀ i, AEMeasurable (X i) μ) (h : iIndepFun X μ)
    (L : NormedSpace.Dual ℝ (Π i, E i)) :
    charFunDual (μ.map fun ω i ↦ X i ω) L =
      ∏ i, charFunDual (μ.map (X i)) (L.comp (.single ℝ E i)) := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map mX).1 h, charFunDual_pi]

lemma iIndepFun.charFunDual_eq_pi' (mX : ∀ i, AEMeasurable (X i) μ) (h : iIndepFun X μ)
    (L : NormedSpace.Dual ℝ (PiLp p E)) :
    charFunDual (μ.map fun ω ↦ (WithLp.equiv p (Π i, E i)).symm fun i ↦ X i ω) L =
      ∏ i, charFunDual (μ.map (X i)) (L.comp
        ((PiLp.continuousLinearEquiv p ℝ E).symm.toContinuousLinearMap.comp (.single ℝ E i))) := by
  change charFunDual (μ.map (_ ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable, (iIndepFun_iff_map_fun_eq_pi_map mX).1 h,
    charFunDual_pi']
  all_goals fun_prop

lemma iIndepFun_iff_charFunDual_eq_pi [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] (mX : ∀ i, AEMeasurable (X i) μ) :
    iIndepFun X μ ↔ ∀ L,
      charFunDual (μ.map fun ω i ↦ X i ω) L =
        ∏ i, charFunDual (μ.map (X i)) (L.comp (.single ℝ E i)) := by
  rw [charFunDual_eq_pi_iff, iIndepFun_iff_map_fun_eq_pi_map mX]

lemma iIndepFun_iff_charFunDual_eq_pi' [∀ i, CompleteSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, SecondCountableTopology (E i)] (mX : ∀ i, AEMeasurable (X i) μ) :
    iIndepFun X μ ↔ ∀ L,
      charFunDual (μ.map fun ω ↦ (WithLp.equiv p (Π i, E i)).symm fun i ↦ X i ω) L =
      ∏ i, charFunDual (μ.map (X i)) (L.comp
        ((PiLp.continuousLinearEquiv p ℝ E).symm.toContinuousLinearMap.comp (.single ℝ E i))) := by
  change _ ↔ ∀ _, charFunDual (μ.map (_ ∘ _)) _ = _
  rw [← AEMeasurable.map_map_of_aemeasurable, charFunDual_eq_pi_iff',
    iIndepFun_iff_map_fun_eq_pi_map mX]
  all_goals fun_prop

end Pi

end NormedSpace

end ProbabilityTheory
