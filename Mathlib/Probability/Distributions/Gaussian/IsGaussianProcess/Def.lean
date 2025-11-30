/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Def

/-!
# Gaussian processes

-/

open MeasureTheory

/-- A stochastic process is a Gaussian process if all its finite dimensional distributions are
Gaussian. -/
@[fun_prop]
public structure ProbabilityTheory.IsGaussianProcess {Ω E T : Type*} {mΩ : MeasurableSpace Ω}
    [MeasurableSpace E] [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (X : T → Ω → E) (P : Measure Ω := by volume_tac) : Prop where
  hasGaussianLaw : ∀ I : Finset T, HasGaussianLaw (fun ω ↦ I.restrict (X · ω)) P
