import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
--import Mathlib

open MeasureTheory Set Filter BoundedContinuousFunction Topology ENNReal NNReal BigOperators



section borel_imp

variable (α : Type _) [MeasurableSpace α]

/-- An event has zero probability if and only if the set has zero measure w.r.t. the probability
measure coerced to a measure. (The content is just to handle the coercions). -/
lemma ProbabilityMeasure.coe_null_iff (μ : ProbabilityMeasure α) (E : Set α) :
    (μ : Measure α) E = 0 ↔ μ E = 0 := by
  constructor <;> intro h
  · simp only [h, zero_toNNReal]
  · simpa only [toNNReal_eq_zero_iff, (measure_lt_top (↑μ) E).ne, or_false] using h

variable [TopologicalSpace α]


/-- One implication of the portmanteau theorem:
Assuming that for all Borel sets `E` whose boundary `∂E` carries no probability mass under a
candidate limit probability measure `μ` we have convergence of the measures `μs i E` to `μ E`,
then for all closed sets `F` we have the limsup condition `limsup (μs i F) ≤ μ F`.

This is a version with coercions to ordinary `ℝ≥0∞`-valued measures. See ??? for
a version with probability measures directly.
-/
lemma borel_condition_implies_closed_condition
    {α ι : Type _} {L : Filter ι} [NeBot L]
    [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]
    {μ : ProbabilityMeasure α} {μs : ι → ProbabilityMeasure α}
    (h : ∀ {E : Set α},
      MeasurableSet E → μ (frontier E) = 0 → Tendsto (fun i ↦ μs i E) L (𝓝 (μ E)))
    (F : Set α) (F_closed : IsClosed F) :
    L.limsup (fun i ↦ (μs i : Measure α) F) ≤ (μ : Measure α) F := by
  have h' : ∀ {E : Set α}, MeasurableSet E → (μ : Measure α) (frontier E) = 0 →
              Tendsto (fun i ↦ (μs i : Measure α) E) L (𝓝 ((μ : Measure α) E)) := by
    intro E E_mble E_nullbdry
    have obs := ENNReal.tendsto_coe.mpr (h E_mble (by simp only [E_nullbdry, zero_toNNReal]))
    simpa only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using obs
  have ex := exists_null_frontiers_thickening μ F
  let rs := Classical.choose ex
  have rs_lim : Tendsto rs atTop (𝓝 0) := (Classical.choose_spec ex).1
  have rs_pos : ∀ n, 0 < rs n := fun n ↦ ((Classical.choose_spec ex).2 n).1
  have rs_null : ∀ n, (μ : Measure α) (frontier (Metric.thickening (rs n) F)) = 0 :=
    fun n ↦ ((Classical.choose_spec ex).2 n).2
  have Fthicks_open : ∀ n, IsOpen (Metric.thickening (rs n) F) :=
    fun n ↦ Metric.isOpen_thickening
  have key := fun (n : ℕ) ↦ h' (Fthicks_open n).measurableSet (rs_null n)
  apply ENNReal.le_of_forall_pos_le_add
  intros ε ε_pos μF_finite
  have keyB := @tendsto_measure_cthickening_of_isClosed α _ _ _ μ F
                ⟨1, ⟨by simp only [gt_iff_lt, zero_lt_one], measure_ne_top _ _⟩⟩ F_closed
  have nhd : Iio ((μ : Measure α) F + ε) ∈ 𝓝 ((μ : Measure α) F) := by
    apply Iio_mem_nhds
    simpa only [add_zero] using ENNReal.add_lt_add_left μF_finite.ne (ENNReal.coe_pos.mpr ε_pos)
  specialize rs_lim (keyB nhd)
  simp only [mem_map, mem_atTop_sets, ge_iff_le, mem_preimage, mem_Iio] at rs_lim
  obtain ⟨m, hm⟩ := rs_lim
  have aux' := fun i ↦
    @measure_mono _ _ (μs i : Measure α) _ _ (Metric.self_subset_thickening (rs_pos m) F)
  have aux : (fun i ↦ ((μs i : Measure α) F))
              ≤ᶠ[L] (fun i ↦ (μs i : Measure α) (Metric.thickening (rs m) F)) := by
    exact eventually_of_forall aux'
  refine (limsup_le_limsup aux).trans ?_
  rw [Tendsto.limsup_eq (key m)]
  apply (measure_mono (Metric.thickening_subset_cthickening (rs m) F)).trans (hm m rfl.le).le

end borel_imp
