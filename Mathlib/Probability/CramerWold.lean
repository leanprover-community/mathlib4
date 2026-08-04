/-
Copyright (c) 2026 Ivo Malinowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivo Malinowski
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Cramèr-Wold Device

We prove one direction of the Cramér-Wold device.

## Main statement

* `tendsto_map_of_tendsto_map_inner`: Given measurable `E`-valued random variables `Xn : ℕ → Ω → E`
  and `X : Ω' → E`, if for every `t : E` the pushforward distributions of the inner products
  `⟪Xn n, t⟫` under `P` converge to the pushforward distribution of `⟪X, t⟫` under `Q`, then the
  distributions of `Xn` under `P` converge to the distribution of `X` under `Q`.

-/

open MeasureTheory Filter Complex BoundedContinuousFunction RealInnerProductSpace ProbabilityMeasure

open scoped Topology

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {Ω : Type*} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω}
  {Ω' : Type*} [MeasurableSpace Ω'] {Q : ProbabilityMeasure Ω'}
  {X : Ω' → E} {Xn : ℕ → Ω → E}

lemma charFun_map_eq_integral_map_inner {α : Type*} {mα : MeasurableSpace α}
  (μ : Measure α) {Y : α → E} (hY : Measurable Y) (t : E) :
  charFun (μ.map Y) t = charFun (μ.map (⟪Y ·, t⟫)) (1 : ℝ) := by
  rw [charFun_apply, charFun_apply_real, integral_map, integral_map]
  · simp
  all_goals fun_prop

lemma tendsto_charFun_of_tendsto_inner (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n))
  (hconv : ∀ t : E, TendstoInDistribution (⟪Xn · ·, t⟫) atTop (⟪X ·, t⟫) (fun _ ↦ P) Q) (t : E) :
  Tendsto (fun n ↦ charFun (P.map (Xn n)) t) atTop (𝓝 (charFun (Q.map X) t)) := by
  let f : ℝ →ᵇ ℂ := innerProbChar (1 : ℝ)
  convert (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp (hconv t).tendsto
    (innerProbChar (1 : ℝ)) using 1
  · ext n
    exact charFun_map_eq_integral_map_inner P (hXn n) t
  · exact congr_arg 𝓝 (charFun_map_eq_integral_map_inner Q hX t)

/-- **Cramér-Wold device (one direction only)**

Convergence in distribution of all 1-dimensional scalar projections of a sequence of
random variables in a finite-dimensional real inner product space implies the
convergence in distribution of the sequence itself. -/
theorem tendsto_map_of_tendsto_map_inner (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n))
    (h : ∀ t, Tendsto (fun n => P.map ((hXn n).inner_const (c := t)).aemeasurable)
      atTop (𝓝 (Q.map (hX.inner_const (c := t)).aemeasurable : ProbabilityMeasure ℝ))) :
    Tendsto (fun n => P.map (hXn n).aemeasurable) atTop (𝓝 (Q.map hX.aemeasurable)) :=
  ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr (tendsto_charFun_of_tendsto_inner hX hXn h)

end
