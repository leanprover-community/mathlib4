/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.HasLaw

/-!
# Bernoulli Distribution

TODO

-/

public section

open MeasureTheory Measure unitInterval
open scoped ENNReal

namespace ProbabilityTheory


variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

@[expose]
noncomputable def bernoulliMeasure (a b : α) (p : I) : Measure α :=
  ENNReal.ofReal p • dirac a + ENNReal.ofReal (σ p) • dirac b

lemma bernoulli_measure_def (a b : α) (p : I) :
    bernoulliMeasure a b p = ENNReal.ofReal p • dirac a + ENNReal.ofReal (σ p) • dirac b := rfl

instance (a b : α) (p : I) : IsProbabilityMeasure (bernoulliMeasure a b p) where
  measure_univ := by simp [bernoulli_measure_def]

@[simp]
theorem bernoulli_measure_self_eq_dirac (a : α) (p : I) :
    bernoulliMeasure a a p = dirac a := by
  simp [bernoulli_measure_def, ← add_smul]

@[simp]
theorem map_bernoulli_measure [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (a b : α) (f : α → β) (p : I) :
    (bernoulliMeasure a b p).map f = bernoulliMeasure (f a) (f b) p := by
  have hf (a : α) : AEMeasurable f (dirac a) := by fun_prop
  simp only [bernoulli_measure_def]
  rw [AEMeasurable.map_add₀ (by fun_prop) (by fun_prop)]
  simp

theorem map_bernoulli_measure' (a b : α) (f : α → β) (hf : Measurable f) (p : I) :
    (bernoulliMeasure a b p).map f = bernoulliMeasure (f a) (f b) p := by
  simp [bernoulli_measure_def, Measure.map_add _ _ hf, Measure.map_smul, map_dirac hf]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem HasLaw.uniform_le_hasLaw (p : I) {U : Ω → I} (hU : HasLaw U ℙ P) :
    HasLaw (U · ≤ p) (bernoulliMeasure True False p) P where
  map_eq := by
    apply ext_of_singleton
    intro prop
    simp_rw [← Function.comp_def (f := (· ≤ p)) (g := U)]
    rw [← AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop),
      map_apply_of_aemeasurable (by fun_prop) (by measurability), hU.map_eq]
    by_cases h : prop
    · simp [h, bernoulli_measure_def, ← Set.mem_Iic]
    · simp [h, bernoulli_measure_def, ← Set.mem_Ioi]

end ProbabilityTheory
