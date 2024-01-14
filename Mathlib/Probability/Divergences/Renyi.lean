/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Divergences.KullbackLeibler

/-!
# Renyi divergences

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

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-- Renyi divergence between two measures. -/
noncomputable def renyiDiv (a : ℝ≥0∞) (μ ν : Measure α) : ℝ :=
  if a = 0 then - log (ν {x | 0 < μ.rnDeriv ν x}).toReal
  else if a = 1 then klReal μ ν
  else if a = ∞ then log (essSup (μ.rnDeriv ν) μ).toReal
  else (a.toReal - 1)⁻¹ * log (∫ x, (μ.rnDeriv ν x).toReal ^ (1 - a.toReal) ∂μ)

end MeasureTheory
