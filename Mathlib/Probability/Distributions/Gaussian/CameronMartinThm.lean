/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Distributions.Gaussian.CameronMartin
import Mathlib.Probability.HasLaw

/-!
# Cameron-Martin Theorem

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

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]
  {μ : Measure E} [IsGaussian μ]

lemma hasLaw_cameronMartin (L : cameronMartinRKHS μ) :
    HasLaw L (gaussianReal 0 (‖L‖₊ ^ 2)) μ where
  map_eq := by
    sorry


end ProbabilityTheory
