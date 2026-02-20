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
import Mathlib.Probability.Process.BrownianMotion
import Aesop

/--
# Ito Integral for Elementary Predictable Processes

This module defines the discrete summation representing the stochastic integral
of an elementary predictable process with respect to a Wiener Process (Brownian Motion).
-/

set_option linter.unusedSectionVars false
noncomputable section
open MeasureTheory ProbabilityTheory TopologicalSpace Filter Finset
open scoped Topology ENNReal MeasureTheory BigOperators

variable {Ω : Type} [m : MeasurableSpace Ω]
variable {F : Filtration ℝ m}
variable {W : StochasticProcess Ω}
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable [wp : WienerProcess W P]

/--
An Elementary Predictable Process represents a trading strategy or a variable
that is piecewise constant and its value at time `t_i` is completely determined
by the information available up to that time (i.e., it is F_{t_i}-measurable).
-/
structure ElementaryPredictableProcess (Ω : Type) where
  -- A finite sequence of time steps
  n : ℕ
  times : Fin (n + 1) → ℝ
  -- Increasing times: t_0 < t_1 < ... < t_n
  ordered : ∀ i : Fin n, times (i.castSucc) < times (i.succ)
  -- The values (strategies) during each interval
  -- Note: We map an index to a random variable Ω → ℝ
  values : Fin n → Ω → ℝ
  -- Predictability: The value chosen for interval [t_i, t_{i+1}) only depends on F_{t_i}
  -- This requires measurable spaces for F. We simplify it conceptually for the architecture here.
  -- adapted_values: ∀ i, StronglyMeasurable (values i) -- (Requires topological real setup)

/--
The core definition of the Ito Integral for an elementary predictable process H
with respect to a Wiener Process W.
This translates to the discrete summation: Σ H_{t_i} * (W_{t_{i+1}} - W_{t_i})
-/
def itoIntegralElementary (H : ElementaryPredictableProcess Ω) : Ω → ℝ :=
  fun ω => ∑ i : Fin H.n, H.values i ω * (W (H.times i.succ) ω - W (H.times i.castSucc) ω)

/--
A fundamental property of the Ito Integral is its linearity.
This theorem states that integrating a scaled process `c * H` scales the integral by `c`.
-/
@[aesop safe]
theorem itoIntegralElementary_smul (c : ℝ) (H : ElementaryPredictableProcess Ω) :
    itoIntegralElementary (W := W) {
      n := H.n,
      times := H.times,
      ordered := H.ordered,
      values := fun i ω => c * H.values i ω
    } = fun ω => c * (itoIntegralElementary (W := W) H ω) := by
  ext ω
  dsimp [itoIntegralElementary]
  -- Use Mathlib's algebraic summation pull-out rule for multiplication
  -- ∑ c * (H * ΔW) = c * ∑ (H * ΔW)
  simp_rw [mul_assoc]
  exact (Finset.mul_sum (Finset.univ) (fun i =>
    H.values i ω * (W (H.times i.succ) ω - W (H.times i.castSucc) ω)) c).symm
