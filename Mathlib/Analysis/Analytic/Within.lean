/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Properties of analyticity restricted to a set

From `Mathlib/Analysis/Analytic/Basic.lean`, we have the definitions

1. `AnalyticWithinAt 𝕜 f s x` means a power series at `x` converges to `f` on `𝓝[insert x s] x`.
2. `AnalyticOn 𝕜 f s t` means `∀ x ∈ t, AnalyticWithinAt 𝕜 f s x`.

This means there exists an extension of `f` which is analytic and agrees with `f` on `s ∪ {x}`, but
`f` is allowed to be arbitrary elsewhere.

Here we prove basic properties of these definitions. Where convenient we assume completeness of the
ambient space, which allows us to relate `AnalyticWithinAt` to analyticity of a local extension.
-/

noncomputable section

open Topology Filter ENNReal

open Set Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-!
### Basic properties
-/

/-- `AnalyticWithinAt` is trivial if `{x} ∈ 𝓝[s] x` -/
lemma analyticWithinAt_of_singleton_mem {f : E → F} {s : Set E} {x : E} (h : {x} ∈ 𝓝[s] x) :
    AnalyticWithinAt 𝕜 f s x := by
  rcases mem_nhdsWithin.mp h with ⟨t, ot, xt, st⟩
  rcases Metric.mem_nhds_iff.mp (ot.mem_nhds xt) with ⟨r, r0, rt⟩
  exact ⟨constFormalMultilinearSeries 𝕜 E (f x), .ofReal r,
  { r_le := by simp only [FormalMultilinearSeries.constFormalMultilinearSeries_radius, le_top]
    r_pos := by positivity
    hasSum := by
      intro y ys yr
      simp only [subset_singleton_iff, mem_inter_iff, and_imp] at st
      simp only [mem_insert_iff, add_eq_left] at ys
      have : x + y = x := by
        rcases ys with rfl | ys
        · simp
        · exact st (x + y) (rt (by simpa using yr)) ys
      simp only [this]
      apply (hasFPowerSeriesOnBall_const (e := 0)).hasSum
      simp only [Metric.emetric_ball_top, mem_univ] }⟩

/-- If `f` is `AnalyticOn` near each point in a set, it is `AnalyticOn` the set -/
lemma analyticOn_of_locally_analyticOn {f : E → F} {s : Set E}
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ AnalyticOn 𝕜 f (s ∩ u)) :
    AnalyticOn 𝕜 f s := by
  intro x m
  rcases h x m with ⟨u, ou, xu, fu⟩
  rcases Metric.mem_nhds_iff.mp (ou.mem_nhds xu) with ⟨r, r0, ru⟩
  rcases fu x ⟨m, xu⟩ with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t,
    { r_pos := lt_min (by positivity) fp.r_pos
      r_le := min_le_of_right_le fp.r_le
      hasSum := by
        intro y ys yr
        simp only [EMetric.mem_ball, lt_min_iff, edist_lt_ofReal, dist_zero_right] at yr
        apply fp.hasSum
        · simp only [mem_insert_iff, add_eq_left] at ys
          rcases ys with rfl | ys
          · simp
          · simp only [mem_insert_iff, add_eq_left, mem_inter_iff, ys, true_and]
            apply Or.inr (ru ?_)
            simp only [Metric.mem_ball, dist_self_add_left, yr]
        · simp only [EMetric.mem_ball, yr] }⟩

/-- On open sets, `AnalyticOnNhd` and `AnalyticOn` coincide -/
lemma IsOpen.analyticOn_iff_analyticOnNhd {f : E → F} {s : Set E} (hs : IsOpen s) :
    AnalyticOn 𝕜 f s ↔ AnalyticOnNhd 𝕜 f s := by
  refine ⟨?_, AnalyticOnNhd.analyticOn⟩
  intro hf x m
  rcases Metric.mem_nhds_iff.mp (hs.mem_nhds m) with ⟨r, r0, rs⟩
  rcases hf x m with ⟨p, t, fp⟩
  exact ⟨p, min (.ofReal r) t,
  { r_pos := lt_min (by positivity) fp.r_pos
    r_le := min_le_of_right_le fp.r_le
    hasSum := by
      intro y ym
      simp only [EMetric.mem_ball, lt_min_iff, edist_lt_ofReal, dist_zero_right] at ym
      refine fp.hasSum ?_ ym.2
      apply mem_insert_of_mem
      apply rs
      simp only [Metric.mem_ball, dist_self_add_left, ym.1] }⟩

/-!
### Equivalence to analyticity of a local extension

We show that `HasFPowerSeriesWithinOnBall`, `HasFPowerSeriesWithinAt`, and `AnalyticWithinAt` are
equivalent to the existence of a local extension with full analyticity.  We do not yet show a
result for `AnalyticOn`, as this requires a bit more work to show that local extensions can
be stitched together.
-/

set_option linter.style.multiGoal false in
/-- `f` has power series `p` at `x` iff some local extension of `f` has that series -/
lemma hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞} :
    HasFPowerSeriesWithinOnBall f p s x r ↔
      ∃ g, EqOn f g (insert x s ∩ EMetric.ball x r) ∧
        HasFPowerSeriesOnBall g p x r := by
  constructor
  · intro h
    refine ⟨fun y ↦ p.sum (y - x), ?_, ?_⟩
    · intro y ⟨ys,yb⟩
      simp only [EMetric.mem_ball, edist_eq_enorm_sub] at yb
      have e0 := p.hasSum (x := y - x) ?_
      have e1 := (h.hasSum (y := y - x) ?_ ?_)
      · simp only [add_sub_cancel] at e1
        exact e1.unique e0
      · simpa only [add_sub_cancel]
      · simpa only [EMetric.mem_ball, edist_zero_eq_enorm]
      · simp only [EMetric.mem_ball, edist_zero_eq_enorm]
        exact lt_of_lt_of_le yb h.r_le
    · refine ⟨h.r_le, h.r_pos, ?_⟩
      intro y lt
      simp only [add_sub_cancel_left]
      apply p.hasSum
      simp only [EMetric.mem_ball] at lt ⊢
      exact lt_of_lt_of_le lt h.r_le
  · intro ⟨g, hfg, hg⟩
    refine ⟨hg.r_le, hg.r_pos, ?_⟩
    intro y ys lt
    rw [hfg]
    · exact hg.hasSum lt
    · refine ⟨ys, ?_⟩
      simpa only [EMetric.mem_ball, edist_eq_enorm_sub, add_sub_cancel_left, sub_zero] using lt

/-- `f` has power series `p` at `x` iff some local extension of `f` has that series -/
lemma hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt [CompleteSpace F] {f : E → F}
    {p : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} :
    HasFPowerSeriesWithinAt f p s x ↔
      ∃ g, f =ᶠ[𝓝[insert x s] x] g ∧ HasFPowerSeriesAt g p x := by
  constructor
  · intro ⟨r, h⟩
    rcases hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mp h with ⟨g, e, h⟩
    refine ⟨g, ?_, ⟨r, h⟩⟩
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, ?_, e⟩
    exact inter_mem_nhdsWithin _ (EMetric.ball_mem_nhds _ h.r_pos)
  · intro ⟨g, hfg, ⟨r, hg⟩⟩
    simp only [eventuallyEq_nhdsWithin_iff, Metric.eventually_nhds_iff] at hfg
    rcases hfg with ⟨e, e0, hfg⟩
    refine ⟨min r (.ofReal e), ?_⟩
    refine hasFPowerSeriesWithinOnBall_iff_exists_hasFPowerSeriesOnBall.mpr ⟨g, ?_, ?_⟩
    · intro y ⟨ys, xy⟩
      refine hfg ?_ ys
      simp only [EMetric.mem_ball, lt_min_iff, edist_lt_ofReal] at xy
      exact xy.2
    · exact hg.mono (lt_min hg.r_pos (by positivity)) (min_le_left _ _)

/-- `f` is analytic within `s` at `x` iff some local extension of `f` is analytic at `x` -/
lemma analyticWithinAt_iff_exists_analyticAt [CompleteSpace F] {f : E → F} {s : Set E} {x : E} :
    AnalyticWithinAt 𝕜 f s x ↔
      ∃ g, f =ᶠ[𝓝[insert x s] x] g ∧ AnalyticAt 𝕜 g x := by
  simp only [AnalyticWithinAt, AnalyticAt, hasFPowerSeriesWithinAt_iff_exists_hasFPowerSeriesAt]
  tauto

/-- `f` is analytic within `s` at `x` iff some local extension of `f` is analytic at `x`. In this
version, we make sure that the extension coincides with `f` on all of `insert x s`. -/
lemma analyticWithinAt_iff_exists_analyticAt' [CompleteSpace F] {f : E → F} {s : Set E} {x : E} :
    AnalyticWithinAt 𝕜 f s x ↔
      ∃ g, f x = g x ∧ EqOn f g (insert x s) ∧ AnalyticAt 𝕜 g x := by
  classical
  simp only [analyticWithinAt_iff_exists_analyticAt]
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hf, hg⟩
    rcases mem_nhdsWithin.1 hf with ⟨u, u_open, xu, hu⟩
    let g' := Set.piecewise u g f
    refine ⟨g', ?_, ?_, ?_⟩
    · have : x ∈ u ∩ insert x s := ⟨xu, by simp⟩
      simpa [g', xu, this] using hu this
    · intro y hy
      by_cases h'y : y ∈ u
      · have : y ∈ u ∩ insert x s := ⟨h'y, hy⟩
        simpa [g', h'y, this] using hu this
      · simp [g', h'y]
    · apply hg.congr
      filter_upwards [u_open.mem_nhds xu] with y hy using by simp [g', hy]
  · rintro ⟨g, -, hf, hg⟩
    exact ⟨g, by filter_upwards [self_mem_nhdsWithin] using hf, hg⟩

alias ⟨AnalyticWithinAt.exists_analyticAt, _⟩ := analyticWithinAt_iff_exists_analyticAt'

lemma AnalyticWithinAt.exists_mem_nhdsWithin_analyticOn
    [CompleteSpace F] {f : E → F} {s : Set E} {x : E} (h : AnalyticWithinAt 𝕜 f s x) :
    ∃ u ∈ 𝓝[insert x s] x, AnalyticOn 𝕜 f u := by
  obtain ⟨g, -, h'g, hg⟩ : ∃ g, f x = g x ∧ EqOn f g (insert x s) ∧ AnalyticAt 𝕜 g x :=
    h.exists_analyticAt
  let u := insert x s ∩ {y | AnalyticAt 𝕜 g y}
  refine ⟨u, ?_, ?_⟩
  · exact inter_mem_nhdsWithin _ ((isOpen_analyticAt 𝕜 g).mem_nhds hg)
  · intro y hy
    have : AnalyticWithinAt 𝕜 g u y := hy.2.analyticWithinAt
    exact this.congr (h'g.mono (inter_subset_left)) (h'g (inter_subset_left hy))
