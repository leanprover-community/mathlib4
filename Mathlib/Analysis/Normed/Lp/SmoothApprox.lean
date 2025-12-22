/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.Tactic.MoveAdd

/-!

# Density of smooth compactly supported functions in `Lp`

In this file, we prove that `Lp` functions can be approximated by smooth compactly supported
functions for `p < ∞`.

This result is recorded in `MeasureTheory.MemLp.exist_sub_eLpNorm_le`.
-/

@[expose] public section

variable {α β E F : Type*} [MeasurableSpace E] [NormedAddCommGroup F]

open scoped Nat NNReal ContDiff
open MeasureTheory Pointwise ENNReal

namespace HasCompactSupport

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedSpace ℝ F]
  (μ : Measure E := by volume_tac) [IsFiniteMeasureOnCompacts μ]

set_option backward.privateInPublic true in
/-- For every continuous compactly supported function `f` there exists a smooth compactly supported
function `g` such that `f - g` is arbitrary small in the `Lp`-norm for `p < ∞`. -/
theorem exist_eLpNorm_sub_le_of_continuous {p : ℝ≥0∞} (hp : p ≠ ⊤) {ε : ℝ} (hε : 0 < ε) {f : E → F}
    (h₁ : HasCompactSupport f) (h₂ : Continuous f) :
    ∃ (g : E → F), HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
    eLpNorm (f - g) p μ ≤ ENNReal.ofReal ε := by
  by_cases hf : f =ᵐ[μ] 0
  -- We will need that the support is non-empty, so we treat the trivial case `f = 0` first.
  · use 0
    simpa [HasCompactSupport.zero, eLpNorm_congr_ae hf] using contDiff_const
  have hs₁ : μ (tsupport f) ≠ ⊤ := h₁.measure_lt_top.ne
  have hs₂ : 0 < (μ <| tsupport f).toReal := by
    -- Since `f` is not the zero function `tsupport f` has positive measure
    rw [← Measure.measure_support_eq_zero_iff _] at hf
    exact toReal_pos (pos_mono (subset_tsupport f) (pos_of_ne_zero hf)).ne' hs₁
  set ε' := ε * (μ <| tsupport f).toReal ^ (-(1 / p.toReal)) with ε'_def
  have hε' : 0 < ε' := by positivity
  have hε₂ : ENNReal.ofReal ε' * μ (tsupport f) ^ (1 / p.toReal) ≤ ENNReal.ofReal ε := by
    rw [← ofReal_toReal hs₁, ofReal_rpow_of_pos hs₂, ← ofReal_mul hε'.le,
      ofReal_le_ofReal_iff hε.le, ε'_def, mul_assoc, ← Real.rpow_add hs₂, neg_add_cancel,
      Real.rpow_zero, mul_one]
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := h₂.exists_contDiff_approx ⊤ (ε := fun _ ↦ ε') (by fun_prop)
    (by intro; positivity)
  refine ⟨g, h₁.mono hg₃, hg₁, (eLpNorm_sub_le_of_dist_bdd μ hp h₁.measurableSet hε'.le ?_
    (subset_tsupport f) (hg₃.trans (subset_tsupport f))).trans hε₂⟩
  intro x
  rw [dist_comm]
  exact (hg₂ x).le

end HasCompactSupport

namespace MeasureTheory.MemLp

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
  [NormedSpace ℝ F]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- Every `Lp` function can be approximated by a smooth compactly supported function provided that
`p < ∞`. -/
theorem exist_eLpNorm_sub_le {p : ℝ≥0∞} (hp : p ≠ ⊤) (hp₂ : 1 ≤ p) {f : E → F} (hf : MemLp f p μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ eLpNorm (f - g) p μ ≤ ENNReal.ofReal ε := by
  -- We use a standard ε / 2 argument to deduce the result from the approximation for
  -- continuous compactly supported functions.
  have hε₂ : 0 < ε / 2 := by positivity
  have hε₂' : 0 < ENNReal.ofReal (ε / 2) := by positivity
  obtain ⟨g, hg₁, hg₂, hg₃, hg₄⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp hε₂'.ne'
  obtain ⟨g', hg'₁, hg'₂, hg'₃⟩ := hg₁.exist_eLpNorm_sub_le_of_continuous μ hp hε₂ hg₃
  refine ⟨g', hg'₁, hg'₂, ?_⟩
  have : f - g' = (f - g) - (g' - g) := by simp
  grw [this, eLpNorm_sub_le (hf.aestronglyMeasurable.sub hg₄.aestronglyMeasurable)
    (hg'₂.continuous.aestronglyMeasurable.sub hg₄.aestronglyMeasurable) hp₂, hg₂,
    eLpNorm_sub_comm, hg'₃, ← ENNReal.ofReal_add hε₂.le hε₂.le, add_halves]

theorem _root_.MeasureTheory.Lp.dense_hasCompactSupport_contDiff {p : ℝ≥0∞} (hp : p ≠ ⊤)
    [hp₂ : Fact (1 ≤ p)] :
    Dense {f : Lp F p μ | ∃ (g : E → F), f =ᵐ[μ] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε ↦ ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := exist_eLpNorm_sub_le hp hp₂.out (Lp.memLp f) hε
  have hg₄ : MemLp g p μ := hg₂.continuous.memLp_of_hasCompactSupport hg₁
  use hg₄.toLp
  use ⟨g, hg₄.coeFn_toLp, hg₁, hg₂⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
    ← le_ofReal_iff_toReal_le ((Lp.memLp f).sub (Lp.memLp hg₄.toLp)).eLpNorm_ne_top hε.le]
  convert hg₃ using 1
  apply eLpNorm_congr_ae
  gcongr
  exact hg₄.coeFn_toLp

end MeasureTheory.MemLp
