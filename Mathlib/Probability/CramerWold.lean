/-
Copyright (c) 2026 Ivo Malinowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivo Malinowski
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Cramèr-Wold Theorem

We prove one direction of the Cramér-Wold theorem.

## Main statement

* `tendsto_map_of_tendsto_map_inner`: Given measurable `E`-valued random variables `Xn : ℕ → Ω → E`
  and `X : Ω' → E`, if for every `t : E` the pushforward distributions of the inner products
  `⟪Xn n, t⟫` under `P` converge to the pushforward distribution of `⟪X, t⟫` under `Q`, then the
  distributions of `Xn` under `P` converge to the distribution of `X` under `Q`.

-/

open MeasureTheory Filter Complex BoundedContinuousFunction RealInnerProductSpace ProbabilityMeasure

open scoped Topology

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']

lemma tendsto_charFun_of_tendsto_inner (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n))
  (hconv : ∀ t : E, TendstoInDistribution (⟪Xn · ·, t⟫) atTop (⟪X ·, t⟫) (fun _ ↦ P) P') (t : E) :
  Tendsto (fun n ↦ charFun (P.map (Xn n)) t) atTop (𝓝 (charFun (P'.map X) t)) := by
  let f : ℝ →ᵇ ℂ := innerProbChar (1 : ℝ)
  convert (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp (hconv t).tendsto
    (innerProbChar (1 : ℝ)) using 1
  · ext n
    exact charFun_map_eq_integral_map_inner P (hXn n) t
  · exact congr_arg 𝓝 (charFun_map_eq_integral_map_inner P' hX t)

variable [FiniteDimensional ℝ E]

/-- **Cramér-Wold theorem (one direction only)**

Convergence in distribution of all scalar projections of a sequence of
random variables in a finite-dimensional real inner product space implies the
convergence in distribution of the sequence itself. -/
theorem tendstoInDistribution_of_inner (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n))
    (h : ∀ t, TendstoInDistribution (⟪Xn · ·, t⟫) atTop (⟪X ·, t⟫) (fun _ ↦ P) P') :
    TendstoInDistribution Xn atTop X (fun _ ↦ P) P' where
  forall_aemeasurable n := (hXn n).aemeasurable
  tendsto :=
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr (tendsto_charFun_of_tendsto_inner hX hXn h)

end
