/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Calculus.MeanValue

/-!
# f-Divergences

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open Real

open scoped ENNReal NNReal Topology

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α}
  {μ ν : Measure α} {f : ℝ → ℝ}

/-- Likelihood ratio composed with a function `f : ℝ → ℝ`. -/
noncomputable
def LRf (f : ℝ → ℝ) (μ ν : Measure α) (x : α) : ℝ := f (μ.rnDeriv ν x).toReal

lemma lrf_def (μ ν : Measure α) : LRf f μ ν = fun x ↦ f (μ.rnDeriv ν x).toReal := rfl

/-- f-Divergence of two measures. -/
noncomputable
def fDiv (f : ℝ → ℝ) (μ ν : Measure α) : ℝ := ∫ x, LRf f μ ν x ∂ν

lemma le_fDiv [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0))
    (hf_int : Integrable (LRf f μ ν) ν) (hμν : μ ≪ ν) :
    f (μ Set.univ).toReal ≤ fDiv f μ ν := by
  calc f (μ Set.univ).toReal
    = f (∫ x, (μ.rnDeriv ν x).toReal ∂ν) := by rw [Measure.integral_toReal_rnDeriv hμν]
  _ ≤ ∫ x, f (μ.rnDeriv ν x).toReal ∂ν := by
    rw [← average_eq_integral, ← average_eq_integral]
    exact ConvexOn.map_average_le hf_cvx hf_cont isClosed_Ici (by simp)
      Measure.integrable_toReal_rnDeriv hf_int
  _ = ∫ x, LRf f μ ν x ∂ν := rfl

lemma fDiv_nonneg [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hf_cvx : ConvexOn ℝ (Set.Ici 0) f) (hf_cont : ContinuousOn f (Set.Ici 0)) (hf_one : f 1 = 0)
    (hf_int : Integrable (LRf f μ ν) ν) (hμν : μ ≪ ν) :
    0 ≤ fDiv f μ ν :=
  calc 0 = f (μ Set.univ).toReal := by simp [hf_one]
  _ ≤ ∫ x, LRf f μ ν x ∂ν := le_fDiv hf_cvx hf_cont hf_int hμν

end MeasureTheory
