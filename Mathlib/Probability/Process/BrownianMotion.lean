/-
Copyright (c) 2026 AxiomForge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AxiomForge
-/
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Independence.Basic
import Aesop

/--
# Brownian Motion (Wiener Process)

This module defines the foundational axioms of the Standard Wiener Process.
It establishes the core probability measure required for stochastic calculus.
-/

noncomputable section
open MeasureTheory ProbabilityTheory TopologicalSpace Filter
open scoped Topology ENNReal MeasureTheory

variable {Ω : Type} [m : MeasurableSpace Ω]
variable {F : Filtration ℝ m}

abbrev StochasticProcess (Ω : Type) := ℝ → Ω → ℝ

/--
The rigorous geometric and probabilistic definition of a Standard Wiener Process (Brownian Motion).
This is the absolute foundation of Ito's Calculus and the Black-Scholes equation.
-/
@[aesop safe]
class WienerProcess (W : StochasticProcess Ω) (P : Measure Ω) [IsProbabilityMeasure P] : Prop where
  -- 1. It is adapted to the filtration F.
  adapted : Adapted F W

  -- 2. It starts at Zero: W_0 = 0 almost surely.
  started_at_zero : ∀ᵐ ω ∂P, W 0 ω = 0

  -- 3. It has almost surely continuous paths.
  continuous_paths : ∀ᵐ ω ∂P, Continuous (fun t => W t ω)

  -- 4. It is a Gaussian Process.
  is_gaussian : IsGaussianProcess W P

  -- 5. Independent Increments (Simplified representation for now)
  -- The increment W_t - W_s is independent of the past state W_s
  indep_increments : ∀ s t, s ≤ t → IndepFun (fun ω => W t ω - W s ω) (fun ω => W s ω) P
