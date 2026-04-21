/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.RCLike.Basic

/-!
# Taylor series converges to function on whole ball

In this file we prove that if a function `f` is analytic on the ball of convergence of its Taylor
series, then the series converges to `f` on this ball.
-/
set_option backward.defeqAttrib.useBackward true

public section

variable {𝕜 : Type*} [RCLike 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜}

/-- If `f` is analytic on `Bᵣ(x₀)` and its Taylor series converges on this ball, then it converges
to `f`. -/
theorem AnalyticOn.hasFPowerSeriesOnSubball
    {r : ENNReal} (hr_pos : 0 < r) (h : AnalyticOn 𝕜 f (Metric.eball x r)) :
    letI p := FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ iteratedDeriv n f x / n.factorial);
    r ≤ p.radius → HasFPowerSeriesOnBall f p x r := by
  rw [Metric.isOpen_eball.analyticOn_iff_analyticOnNhd] at h
  intro hr
  set p := FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ iteratedDeriv n f x / n.factorial)
  let g (t : 𝕜) := p.sum (t - x)
  have hg : HasFPowerSeriesOnBall g p x p.radius := by
    simpa using (p.hasFPowerSeriesOnBall (by order)).comp_sub x
  have hg' : AnalyticOnNhd 𝕜 g (Metric.eball x p.radius) := by
    simpa using p.analyticOnNhd.comp_sub x
  replace hg' : AnalyticOnNhd 𝕜 g (Metric.eball x r) := hg'.mono (Metric.eball_subset_eball hr)
  apply h.eqOn_of_preconnected_of_eventuallyEq at hg'
  apply (hg.mono hr_pos hr).congr
  symm
  apply hg' (Metric.isConnected_eball hr_pos).isPreconnected (show x ∈ Metric.eball x r by simpa) ?_
  have hf : AnalyticAt 𝕜 f x := h _ (by simp [hr_pos])
  apply AnalyticAt.hasFPowerSeriesAt at hf
  unfold Filter.EventuallyEq Filter.Eventually
  rw [EMetric.mem_nhds_iff]
  obtain ⟨ε, hf⟩ := hf
  exact ⟨ε, hf.r_pos, hf.unique (hg.mono hf.r_pos hf.r_le)⟩

/-- If `f` is analytic on the ball of convergence of its Taylor series, then the series converges
to `f` on this ball. This is a stronger version of `AnalyticAt.hasFPowerSeriesAt` that requires
the assumption `RCLike 𝕜`.

For example, over the `p`-adic numbers, the indicator function of the unit ball is
analytic everywhere, but it agrees with the sum of its Taylor series only on this unit ball. -/
theorem AnalyticOn.hasFPowerSeriesOnBall :
    letI p := FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ iteratedDeriv n f x / n.factorial);
    0 < p.radius → AnalyticOn 𝕜 f (Metric.eball x p.radius) →
    HasFPowerSeriesOnBall f p x p.radius := by
  intro hr hs
  exact hs.hasFPowerSeriesOnSubball hr le_rfl
