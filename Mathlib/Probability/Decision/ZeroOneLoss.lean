/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import Mathlib.Probability.Decision.Risk.Basic

/-!
# Risk for the 0-1 Loss

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Θ 𝓧 : Type*} {mΘ : MeasurableSpace Θ} {m𝓧 : MeasurableSpace 𝓧}
  {P : Kernel Θ 𝓧} {π : Measure Θ}

def zeroOneLoss (Θ : Type*) [DecidableEq Θ] (θ y : Θ) : ℝ≥0∞ := if θ = y then 0 else 1

lemma zeroOneLoss_eq_indicator [DecidableEq Θ] :
    zeroOneLoss Θ = fun θ ↦ {y | y ≠ θ}.indicator 1 := by
  ext θ y
  classical
  simp [zeroOneLoss, Set.indicator_apply, eq_comm]

@[simp]
lemma integral_zeroOneLoss [DecidableEq Θ] [MeasurableSingletonClass Θ] (ν : Measure Θ) (θ : Θ) :
    ∫⁻ y, zeroOneLoss Θ θ y ∂ν = ν {y | y ≠ θ} := by
  rw [zeroOneLoss_eq_indicator, lintegral_indicator_one]
  exact measurableSet_eq.compl

end ProbabilityTheory
