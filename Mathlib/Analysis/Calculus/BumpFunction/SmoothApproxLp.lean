/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Tactic.MoveAdd

/-!

# Density of smooth compactly supported functions in `Lp`

In this file, we prove that `Lp` functions can be approximated by smooth compactly supported
functions for `p < ∞`.

This result is recorded in `MeasureTheory.MemLp.exist_sub_eLpNorm_le`.
-/


variable {α β E F : Type*} [MeasurableSpace E] [NormedAddCommGroup F]

open scoped Nat NNReal ContDiff
open MeasureTheory Pointwise ENNReal

theorem MeasureTheory.eLpNorm_sub_le_of_dist_bdd' (μ : Measure E := by volume_tac)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) {c : ℝ} (hc : 0 ≤ c) {f g : E → F} {s : Set E}
    (h : ∀ x, dist (f x) (g x) ≤ c) (hs : MeasurableSet s) (hs₁ : f.support ⊆ s)
    (hs₂ : g.support ⊆ s) :
    eLpNorm (f - g) p μ ≤ ENNReal.ofReal c * μ s ^ (1 / p.toReal) := by
  have hs₃ : s.indicator (f - g) = f - g := by
    rw [Set.indicator_eq_self]
    exact (Function.support_sub _ _).trans (Set.union_subset hs₁ hs₂)
  rw [← hs₃]
  exact eLpNorm_sub_le_of_dist_bdd μ hp hs hc (fun x _ ↦ h x)

namespace HasCompactSupport

/-- Every continuous compactly supported function is in `Lp` for every `p`. -/
theorem memLp_of_continuous [TopologicalSpace E] [Nonempty E] [OpensMeasurableSpace E]
    [SecondCountableTopologyEither E F] (μ : Measure E := by volume_tac)
    [IsFiniteMeasureOnCompacts μ]
    {p : ℝ≥0∞} {f : E → F} (h₁ : HasCompactSupport f) (h₂ : Continuous f) : MemLp f p μ := by
  obtain ⟨x₀, hx₀⟩ := h₂.norm.exists_forall_ge_of_hasCompactSupport h₁.norm
  exact h₁.memLp_of_bound h₂.aestronglyMeasurable ‖f x₀‖ (ae_of_all _ hx₀)

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]
variable [CompleteSpace F] [NormedSpace ℝ F]

/-- For every continuous compactly supported function `f`, there exists a smooth compactly supported
function `g` that increases the support by `1` and `dist (g x) (f x)` is arbitrary small.

The function `g` is explicitly constructed using convolution with a bump function. -/
theorem exist_support_subset_cthickening {μ : Measure E} [μ.IsAddHaarMeasure] {p : ℝ≥0∞}
    (hp₂ : 1 ≤ p) {ε : ℝ} (hε : 0 < ε) {f : E → F}
    (h₁ : HasCompactSupport f) (h₂ : Continuous f) (h₃ : MemLp f p μ) :
    ∃ (g : E → F), HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      g.support ⊆ Metric.cthickening 1 (tsupport f) ∧ ∀ x, dist (f x) (g x) ≤ ε := by
  have := h₁.uniformContinuous_of_continuous h₂
  rw [Metric.uniformContinuous_iff] at this
  rcases this ε hε with ⟨δ', hδ', h⟩
  set δ := min δ' 1
  have hδ₁ : 0 < δ := by positivity
  have hδ₂ : δ ≤ 1 := inf_le_right
  set phi : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ₁, half_lt_self hδ₁⟩
  set g' := MeasureTheory.convolution (phi.normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ
  have hg'₁ : ContDiff ℝ ∞ g' :=
    phi.hasCompactSupport_normed.contDiff_convolution_left _ phi.contDiff_normed
      (h₃.locallyIntegrable hp₂)
  have hg'₂ : HasCompactSupport g' := phi.hasCompactSupport_normed.convolution _ h₁
  refine ⟨g', hg'₂, hg'₁, ?_, fun x ↦ ?_⟩
  · grw [MeasureTheory.support_convolution_subset, ContDiffBump.support_normed_eq, ball_add,
      zero_vadd, Metric.thickening_mono hδ₂, Metric.thickening_subset_cthickening,
      Metric.cthickening_subset_of_subset]
    exact subset_tsupport f
  rw [dist_comm]
  apply ContDiffBump.dist_normed_convolution_le h₃.1
  intro x₀ hx₀
  exact (h (lt_of_lt_of_le hx₀ inf_le_left)).le

/-- For every continuous compactly supported function `f`there exists a smooth compactly supported
function `g` such that `f - g` is arbitrary small in the `Lp`-norm for `p < ∞`. -/
theorem exist_sub_eLpNorm_le_of_continuous (μ : Measure E := by volume_tac) [μ.IsAddHaarMeasure]
    {p : ℝ≥0∞} (hp : p ≠ ⊤) (hp₂ : 1 ≤ p) {ε : ℝ}
    (hε : 0 < ε) {f : E → F} (h₁ : HasCompactSupport f) (h₂ : Continuous f) :
    ∃ (g : E → F), HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
    eLpNorm (f - g) p μ ≤ ENNReal.ofReal ε := by
  by_cases hf : f = 0
  -- Later, we need that the support is non-empty, so we treat the trivial case `f = 0` first.
  · use 0
    simpa [HasCompactSupport.zero, hf] using contDiff_const
  set s := Metric.cthickening 1 (tsupport f)
  have hs₁ : IsCompact s := h₁.cthickening
  have hs₁' : μ s ≠ ⊤ := hs₁.measure_lt_top.ne
  have hs₂ : 0 < (μ s).toReal := by
    -- Since `f` is not the zero function `s` has positive measure
    apply ENNReal.toReal_pos _ hs₁'
    apply (MeasureTheory.pos_mono (Metric.thickening_subset_cthickening _ _) _).ne'
    apply Metric.isOpen_thickening.measure_pos μ
    apply (Metric.thickening_nonempty_iff.mpr ⟨zero_lt_one, ?_⟩)
    rw [← tsupport_eq_empty_iff] at hf
    exact Set.nonempty_iff_ne_empty.mpr hf
  set ε' := ε * (μ s).toReal ^ (- p.toReal⁻¹)
  have hε' : 0 < ε' := by positivity
  have hε₂ : ENNReal.ofReal ε' * μ s ^ (1 / p.toReal) ≤ ENNReal.ofReal ε := by
    have : μ s ^ (1 / p.toReal) ≠ ⊤ := by simp [hs₁']
    rw [← ENNReal.ofReal_toReal this, ← ENNReal.ofReal_mul hε'.le]
    refine ENNReal.ofReal_le_ofReal_iff'.mpr ?_
    left
    unfold ε'
    rw [← ENNReal.toReal_rpow]
    move_mul [ε]
    rw [← Real.rpow_add, one_div, neg_add_cancel, Real.rpow_zero, one_mul]
    exact hs₂
  obtain ⟨g, hg₁, hg₂, hg₃, hg₄⟩ := h₁.exist_support_subset_cthickening hp₂ hε' h₂
    (h₁.memLp_of_continuous μ h₂)
  have hf : Function.support f ⊆ Metric.cthickening 1 (tsupport f) := by
    intro x hx
    simp [EMetric.infEdist_zero_of_mem (subset_tsupport _ hx)]
  exact ⟨g, hg₁, hg₂,
    (eLpNorm_sub_le_of_dist_bdd' μ hp hε'.le hg₄ hs₁.measurableSet hf hg₃).trans hε₂⟩

/-- Every `Lp` function can be approximated by a smooth compactly supported function provided that
`p < ∞`. -/
theorem _root_.MeasureTheory.MemLp.exist_sub_eLpNorm_le {μ : Measure E} [μ.IsAddHaarMeasure]
    {p : ℝ≥0∞} (hp : p ≠ ⊤) (hp₂ : 1 ≤ p) {f : E → F} (hf : MemLp f p μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ eLpNorm (f - g) p μ ≤ ENNReal.ofReal ε := by
  -- We use a standard ε/2 argument to deduce the result from the approximation for
  -- continuous compactly supported functions.
  have hε₂ : 0 < ε/2 := by positivity
  have hε₂' : 0 < ENNReal.ofReal (ε/2) := by positivity
  obtain ⟨g, hg₁, hg₂, hg₃, hg₄⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp hε₂'.ne'
  obtain ⟨g', hg'₁, hg'₂, hg'₃⟩ := hg₁.exist_sub_eLpNorm_le_of_continuous μ hp hp₂ hε₂ hg₃
  refine ⟨g', hg'₁, hg'₂, ?_⟩
  have : f - g' = (f - g) - (g' - g) := by simp
  grw [this, eLpNorm_sub_le (hf.aestronglyMeasurable.sub hg₄.aestronglyMeasurable)
    (hg'₂.continuous.aestronglyMeasurable.sub hg₄.aestronglyMeasurable) hp₂, hg₂,
    eLpNorm_sub_comm, hg'₃, ← ENNReal.ofReal_add hε₂.le hε₂.le, add_halves]

end HasCompactSupport
