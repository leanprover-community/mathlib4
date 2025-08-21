/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.RCLike.Basic

/-!
# Taylor series converges to function on whole ball

In this file we prove that if a function `f` is analytic on the ball of convergence of its Taylor
series, then the series converges to `f` on this ball.
-/

/-- If `f` is analytic on `Bᵣ(x₀)` and its Taylor series converges on this ball, then it converges
to `f`. -/
theorem AnalyticOn_subball_hasFPowerSeriesOnBall {𝕜 : Type*} [RCLike 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜}
    {r : ENNReal} (hr_pos : 0 < r) (h : AnalyticOn 𝕜 f (EMetric.ball x r)) :
    let p := FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ iteratedDeriv n f x / n.factorial);
    r ≤ p.radius → HasFPowerSeriesOnBall f p x r := by
  rw [EMetric.isOpen_ball.analyticOn_iff_analyticOnNhd] at h
  intro p hr
  let g (t : 𝕜) := p.sum (t - x)
  have hg : HasFPowerSeriesOnBall g p x p.radius := by
    simpa using
      (p.hasFPowerSeriesOnBall (lt_of_lt_of_le hr_pos hr)).comp_sub x
  have hg' : AnalyticOnNhd 𝕜 g (EMetric.ball x p.radius) := by
    simpa using AnalyticOnNhd.comp_sub p.analyticOnNhd x
  replace hg' : AnalyticOnNhd 𝕜 g (EMetric.ball x r) :=
    hg'.mono (EMetric.ball_subset_ball hr)
  apply h.eqOn_of_preconnected_of_eventuallyEq at hg'
  apply (hg.mono hr_pos hr).congr
  symm
  apply hg' (IsConnected.isPreconnected (Metric.isConnected_eball hr_pos))
    (show x ∈ EMetric.ball x r by simpa) ?_
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
theorem AnalyticOn.hasFPowerSeriesOnBall {𝕜 : Type*} [RCLike 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜} :
    let p := FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ iteratedDeriv n f x / n.factorial);
    0 < p.radius → AnalyticOn 𝕜 f (EMetric.ball x p.radius) →
    HasFPowerSeriesOnBall f p x p.radius := by
  intro p hr hs
  exact AnalyticOn_subball_hasFPowerSeriesOnBall hr hs (by rfl)
