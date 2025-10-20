import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Function.UniformIntegrable


variable {𝕜 𝕜' D E F G R V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F]
variable
  [MeasurableSpace E]
  [FiniteDimensional ℝ E]

open scoped Nat NNReal ContDiff
open SchwartzMap MeasureTheory
open Pointwise

variable {μ : Measure E} [μ.IsAddHaarMeasure]

variable [OpensMeasurableSpace E] in
theorem HasCompactSupport.memLp_of_continuous {p : ENNReal} {f : E → F} (h₁ : HasCompactSupport f)
    (h₂ : Continuous f) : MemLp f p μ := by
  obtain ⟨x₀, hx₀⟩ := h₂.norm.exists_forall_ge_of_hasCompactSupport h₁.norm
  apply h₁.memLp_of_bound h₂.aestronglyMeasurable ‖f x₀‖
  apply ae_of_all
  exact hx₀

variable [CompleteSpace F] [BorelSpace E]

variable [NormedSpace ℝ F]

theorem exist_eLpNorm₁ {p : ENNReal} (hp₂ : 1 ≤ p) {ε : ℝ} (hε : 0 < ε) {f : E → F}
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

theorem exist_eLpNorm₂ {p : ENNReal} (hp : p ≠ ⊤) (hp₂ : 1 ≤ p) {ε : ℝ} (hε : 0 < ε) {f : E → F}
    (h₁ : HasCompactSupport f) (h₂ : Continuous f) (h₃ : MemLp f p μ) :
    ∃ (g : E → F), HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
    eLpNorm (g - f) p μ ≤ ENNReal.ofReal ε := by
  by_cases hf : f = 0
  · use 0
    simp [hf, HasCompactSupport.zero]
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
    apply (Function.support_sub _ _).trans
    apply Set.union_subset hg₃
    simp only [Function.support_subset_iff, ne_eq, Metric.mem_cthickening_iff, ENNReal.ofReal_one]
    intro x hx
    rw [EMetric.infEdist_zero_of_mem (subset_tsupport _ hx)]
    exact zero_le_one
  grw [← hs₃]
  exact (eLpNorm_sub_le_of_dist_bdd μ hp hs₁.measurableSet hε'.le (fun x _ ↦ hg₄ x)).trans hε₂

theorem exist_eLpNorm₃ {p : ENNReal} (hp : p ≠ ⊤) (hp₂ : 1 ≤ p) {f : E → F} (hf : MemLp f p μ)
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

theorem SchwartzMap.denseRange_toLpCLM {p : ENNReal} (hp : p ≠ ⊤) [hp' : Fact (1 ≤ p)] :
    DenseRange (SchwartzMap.toLpCLM ℝ F p μ) := by
  intro f
  refine (mem_closure_iff_nhds_basis EMetric.nhds_basis_closed_eball).2 fun ε hε ↦ ?_
  by_cases hε' : ε ≠ ⊤
  · obtain ⟨g, hg₁, hg₂, hg₃⟩ := exist_eLpNorm₃ hp hp'.out (Lp.memLp f)
      (ENNReal.toReal_pos hε.ne' hε')
    rw [ENNReal.ofReal_toReal hε'] at hg₁
    use (hg₂.toSchwartzMap hg₃).toLp p μ
    rw [EMetric.mem_closedBall']
    simp only [Set.mem_range, toLpCLM_apply, exists_apply_eq_apply,
      true_and]
    rw [Lp.edist_def]
    have : (f : E → F) - ((hg₂.toSchwartzMap hg₃).toLp p μ : E → F) =ᶠ[ae μ] (f : E → F) - g := by
      filter_upwards [(hg₂.toSchwartzMap hg₃).coeFn_toLp p μ]
      simp
    rwa [eLpNorm_congr_ae this]
  simp at hε'
  rw [hε']
  use (0 : 𝓢(E, F)).toLp p μ
  simp only [Set.mem_range, toLpCLM_apply, EMetric.closedBall_top, Set.mem_univ, and_true]
  use 0
