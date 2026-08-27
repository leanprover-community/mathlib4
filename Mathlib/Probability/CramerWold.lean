/-
Copyright (c) 2026 Ivo Malinowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivo Malinowski
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Cramér-Wold Theorem

We prove the Cramér-Wold theorem.

## Main statement

* `tendstoInDistribution_iff_tendstoInDistribution_inner`: For `E`-valued random variables
  `X : ℕ → Ω → E` and `X' : Ω' → E`, convergence in distribution of `X` under `P` to `X'` under
  `P'` is equivalent to convergence in distribution of all their scalar projections.

-/

open MeasureTheory Filter RealInnerProductSpace

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X' : Ω' → E} {X : ℕ → Ω → E}

/-- The **Cramér-Wold theorem**: convergence in distribution of a sequence of random variables
taking values in a finite-dimensional real inner product space is equivalent to convergence in
distribution of all its scalar projections. -/
theorem tendstoInDistribution_iff_tendstoInDistribution_inner
    (hX' : AEMeasurable X' P') (hX : ∀ n, AEMeasurable (X n) P) :
    TendstoInDistribution X atTop X' (fun _ ↦ P) P' ↔
    (∀ t, TendstoInDistribution (⟪X · ·, t⟫) atTop (⟪X' ·, t⟫) (fun _ ↦ P) P') where
  mp h t := h.continuous_comp (continuous_id.inner continuous_const)
  mpr h := by
    refine .of_tendsto_charFun hX hX' fun t ↦ ?_
    rw [charFun_map_eq_charFun_map_inner_one hX']
    refine (h t).tendsto_charFun 1 |>.congr fun n ↦ ?_
    rw [charFun_map_eq_charFun_map_inner_one (hX n)]

alias ⟨_, TendstoInDistribution.of_inner⟩ := tendstoInDistribution_iff_tendstoInDistribution_inner

end
