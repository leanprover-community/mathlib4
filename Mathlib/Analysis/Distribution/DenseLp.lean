/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Function.UniformIntegrable


/-!

# Density of smooth compactly supported functions in `Lp`

-/


variable {𝕜 𝕜' D E F G R V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F]

open scoped Nat NNReal ContDiff
open SchwartzMap MeasureTheory Pointwise ENNReal

variable {μ : Measure E} [μ.IsAddHaarMeasure]

variable [OpensMeasurableSpace E] in
theorem HasCompactSupport.memLp_of_continuous {p : ℝ≥0∞} {f : E → F} (h₁ : HasCompactSupport f)
    (h₂ : Continuous f) : MemLp f p μ := by
  obtain ⟨x₀, hx₀⟩ := h₂.norm.exists_forall_ge_of_hasCompactSupport h₁.norm
  exact h₁.memLp_of_bound h₂.aestronglyMeasurable ‖f x₀‖ (ae_of_all _ hx₀)

variable [BorelSpace E]
  [CompleteSpace F] [NormedSpace ℝ F]

theorem exist_eLpNorm₁ {p : ℝ≥0∞} (hp₂ : 1 ≤ p) {ε : ℝ} (hε : 0 < ε) {f : E → F}
    (h₁ : HasCompactSupport f) (h₂ : Continuous f) (h₃ : MemLp f p μ) :
    ∃ (g : E → F), HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      g.support ⊆ Metric.cthickening 1 (tsupport f) ∧ ∀ x, dist (g x) (f x) ≤ ε := by
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
  apply ContDiffBump.dist_normed_convolution_le h₃.1
  intro x₀ hx₀
  exact (h (lt_of_lt_of_le hx₀ inf_le_left)).le

theorem exist_eLpNorm₂ {p : ℝ≥0∞} (hp : p ≠ ⊤) (hp₂ : 1 ≤ p) {ε : ℝ} (hε : 0 < ε) {f : E → F}
    (h₁ : HasCompactSupport f) (h₂ : Continuous f) (h₃ : MemLp f p μ) :
    ∃ (g : E → F), HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
    eLpNorm (g - f) p μ ≤ ENNReal.ofReal ε := by
  by_cases hf : f = 0
  · use 0
    simp only [HasCompactSupport.zero, hf, sub_self, eLpNorm_zero, zero_le, and_true, true_and]
    exact contDiff_const
  set s := Metric.cthickening 1 (tsupport f)
  have hs₁ : IsCompact s := h₁.cthickening
  have hs₁' : μ s ≠ ⊤ := hs₁.measure_lt_top.ne
  have hs₂ : 0 < (μ s).toReal := by
    apply ENNReal.toReal_pos _ hs₁'
    apply (MeasureTheory.pos_mono (Metric.thickening_subset_cthickening _ _) _).ne'
    refine Metric.isOpen_thickening.measure_pos μ ?_
    rw [Metric.thickening_nonempty_iff]
    refine ⟨zero_lt_one, ?_⟩
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
  obtain ⟨g, hg₁, hg₂, hg₃, hg₄⟩ := exist_eLpNorm₁ hp₂ hε' h₁ h₂ h₃
  refine ⟨g, hg₁, hg₂, ?_⟩
  have hs₃ : s.indicator (g - f) = g - f := by
    rw [Set.indicator_eq_self]
    apply (Function.support_sub _ _).trans (Set.union_subset hg₃ _)
    simp only [Function.support_subset_iff, ne_eq, Metric.mem_cthickening_iff, ENNReal.ofReal_one]
    intro x hx
    rw [EMetric.infEdist_zero_of_mem (subset_tsupport _ hx)]
    exact zero_le_one
  grw [← hs₃]
  exact (eLpNorm_sub_le_of_dist_bdd μ hp hs₁.measurableSet hε'.le (fun x _ ↦ hg₄ x)).trans hε₂

theorem exist_eLpNorm₃ {p : ℝ≥0∞} (hp : p ≠ ⊤) (hp₂ : 1 ≤ p) {f : E → F} (hf : MemLp f p μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g, eLpNorm (f - g) p μ ≤ ENNReal.ofReal ε ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g := by
  have hε₂ : 0 < ε/2 := by positivity
  have hε₂' : 0 < ENNReal.ofReal (ε/2) := by positivity
  obtain ⟨g, hg₁, hg₂, hg₃, hg₄⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le hp hε₂'.ne'
  obtain ⟨g', hg'₁, hg'₂, hg'₃⟩ := exist_eLpNorm₂ hp hp₂ hε₂ hg₁ hg₃ hg₄
  have hg'₄ : MemLp g' p μ := hg'₁.memLp_of_continuous hg'₂.continuous
  refine ⟨g', ?_, hg'₁, hg'₂⟩
  have : f - g' = (f - g) - (g' - g) := by simp
  grw [this, eLpNorm_sub_le (hf.aestronglyMeasurable.sub hg₄.aestronglyMeasurable)
    (hg'₄.aestronglyMeasurable.sub hg₄.aestronglyMeasurable) hp₂, hg₂, hg'₃]
  rw [← ENNReal.ofReal_add hε₂.le hε₂.le, add_halves]

/-- Schwartz functions are dense in `Lp`. -/
theorem SchwartzMap.denseRange_toLpCLM {p : ℝ≥0∞} (hp : p ≠ ⊤) [hp' : Fact (1 ≤ p)] :
    DenseRange (SchwartzMap.toLpCLM ℝ F p μ) := by
  intro f
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε ↦ ?_
  obtain ⟨g, hg₁, hg₂, hg₃⟩ := exist_eLpNorm₃ hp hp'.out (Lp.memLp f) hε
  use (hg₂.toSchwartzMap hg₃).toLp p μ
  have : (f : E → F) - ((hg₂.toSchwartzMap hg₃).toLp p μ : E → F) =ᶠ[ae μ] (f : E → F) - g := by
    filter_upwards [(hg₂.toSchwartzMap hg₃).coeFn_toLp p μ]
    simp
  simp only [Set.mem_range, toLpCLM_apply, exists_apply_eq_apply, Metric.mem_closedBall', true_and,
    Lp.dist_def, eLpNorm_congr_ae this]
  grw [hg₁, ENNReal.toReal_ofReal hε.le]
  simp
