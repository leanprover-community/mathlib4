/-
Copyright (c) 2026 Ivo Malinowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivo Malinowski
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Cramèr-Wold Theorem

We prove one direction of the Cramér-Wold theorem.

## Main statement

* `tendsto_map_of_tendsto_map_inner`: Given measurable `E`-valued random variables `X : ℕ → Ω → E`
  and `X' : Ω' → E`, if for every `t : E` the pushforward distributions of the inner products
  `⟪X n, t⟫` under `P` converge to the pushforward distribution of `⟪X', t⟫` under `Q`, then the
  distributions of `X` under `P` converge to the distribution of `X'` under `Q`.

-/

open MeasureTheory Filter Complex BoundedContinuousFunction RealInnerProductSpace ProbabilityMeasure

open scoped Topology

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X' : Ω' → E} {X : ℕ → Ω → E}

/-- **Cramér-Wold theorem (one direction only)**

Convergence in distribution of all scalar projections of a sequence of
random variables in a finite-dimensional real inner product space implies the
convergence in distribution of the sequence itself. -/
theorem tendstoInDistribution_of_inner (hX' : AEMeasurable X' P') (hX : ∀ n, AEMeasurable (X n) P)
    (h : ∀ t, TendstoInDistribution (⟪X · ·, t⟫) atTop (⟪X' ·, t⟫) (fun _ ↦ P) P') :
    TendstoInDistribution X atTop X' (fun _ ↦ P) P' where
  forall_aemeasurable n := (hX n)
  tendsto := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
    intro t
    convert
      (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
        (h t).tendsto (innerProbChar (1 : ℝ)) using 1
    · ext n
      exact charFun_map_eq_integral_map_inner P (hX n) t
    · exact congr_arg 𝓝 (charFun_map_eq_integral_map_inner P' hX' t)

end
