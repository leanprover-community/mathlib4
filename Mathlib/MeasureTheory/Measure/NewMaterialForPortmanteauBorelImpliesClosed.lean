import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib

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

/-
#check integrable_indicator_iff
#check integrable_indicatorConstLp
#check lintegral_indicator_const

#check aestronglyMeasurable_indicator_iff
--#check measurable_indicator
#check Measurable.indicator
--#check indicator_measurable

lemma integrable_indicator_const_iff [MeasurableSpace α] (μ : Measure α) {A : Set α}
    [NormedAddCommGroup E] [MeasurableSpace E] (c : E) :
    Integrable (A.indicator (fun _ ↦ c)) μ ↔ (c = 0 ∨ (MeasurableSet A ∧ μ A ≠ ∞)) := by
  constructor <;> intro h
  · by_cases hc : c = 0
    · exact Or.inl hc
    · simp only [hc, ne_eq, false_or]
      have : A = (A.indicator (fun _ ↦ c)) ⁻¹' {c} := by
        ext
        --apply?
        sorry
      sorry
  · by_cases hc : c = 0
    · simp only [hc, indicator_zero, integrable_zero]
    · simp only [hc, ne_eq, false_or] at h
      rcases h with ⟨A_mble, meas_A⟩
      refine ⟨?_, ?_⟩
      · have : Measurable (A.indicator (fun _ ↦ c)) := by
          --have := measurable_indicator_con
          --apply?
          sorry
        --apply Measurable.aestronglyMeasurable
        sorry
      · sorry

lemma integrable_indicator_one_iff [MeasurableSpace α] (μ : Measure α) {A : Set α}
    [NormedAddCommGroup E] (c : E) :
    Integrable (A.indicator (fun _ ↦ c)) μ ↔ MeasurableSet A ∧ (c = 0 ∨ μ A ≠ ∞) := by
  sorry

-- NOTE: Missing?
/-- If `μ` is a finite measure and the indicators of measurable sets `As i` tend pointwise to
the indicator of a set `A` (along a countably generated filter), then the measures `μ (As i)`
tend to the measure `μ A`. -/
lemma tendsto_measure_of_tendsto_indicator'
    {α ι : Type _} (L : Filter ι) [IsCountablyGenerated L]
    [MeasurableSpace α] (μ : Measure α) {A : Set α} (A_mble : MeasurableSet A)
    {As : ι → Set α} (As_mble : ∀ i, MeasurableSet (As i))
    (h_finmeas : ∀ᶠ i in L, μ (As i) < ∞)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  simp_rw [← MeasureTheory.lintegral_indicator_one A_mble, ← MeasureTheory.lintegral_indicator_one (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ≥0∞))
          (eventually_of_forall ?_) (eventually_of_forall ?_) ?_ h_lim
  · exact fun i ↦ Measurable.indicator measurable_const (As_mble i)
  · exact fun i ↦ eventually_of_forall (fun x ↦ indicator_apply_le (fun _ ↦ le_refl _))
  · rw [lintegral_one]
    exact (measure_lt_top μ univ).ne

/-- If `μ` is a finite measure and the indicators of measurable sets `As i` tend pointwise to
the indicator of a set `A` (along a countably generated filter), then the measures `μ (As i)`
tend to the measure `μ A`. -/
lemma tendsto_measure_of_tendsto_indicator
    {α ι : Type _} (L : Filter ι) [IsCountablyGenerated L]
    [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] {A : Set α} (A_mble : MeasurableSet A)
    {As : ι → Set α} (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  simp_rw [← MeasureTheory.lintegral_indicator_one A_mble, ← MeasureTheory.lintegral_indicator_one (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ≥0∞))
          (eventually_of_forall ?_) (eventually_of_forall ?_) ?_ h_lim
  · exact fun i ↦ Measurable.indicator measurable_const (As_mble i)
  · exact fun i ↦ eventually_of_forall (fun x ↦ indicator_apply_le (fun _ ↦ le_refl _))
  · rw [lintegral_one]
    exact (measure_lt_top μ univ).ne
 -/

/-
/-- If `μ` is a finite measure (on an `OpensMeasurableSpace`), then for any set `E`,
the measures of the δ-thickenings of `E` tend to the measure of the closure of `E`
as δ>0 tends to zero. -/
lemma tendsto_measure_thickening_nhds_measure_closure
    {α : Type _} [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {E : Set α} :
    Tendsto (fun δ ↦ μ (Metric.thickening δ E)) (𝓝[>] (0 : ℝ)) (𝓝 (μ (closure E))) := by
  refine tendsto_measure_of_tendsto_indicator (𝓝[>] (0 : ℝ)) μ measurableSet_closure
          (fun δ ↦ (@Metric.isOpen_thickening _ _ δ E).measurableSet) ?_
  apply eventually_of_forall
  intro x
  have key := tendsto_indicator_thickening_indicator_closure (fun _ ↦ (1 : ℝ≥0∞)) E
  rw [tendsto_pi_nhds] at key
  exact key x

/-- If `μ` is a finite measure (on an `OpensMeasurableSpace`), then for any closed set `F`,
the measures of the δ-thickenings of `F` tend to the measure of `F` as δ>0 tends to zero. -/
lemma tendsto_measure_thickening_of_isClosed
    {α : Type _} [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {F : Set α} (F_closed : IsClosed F) :
    Tendsto (fun δ ↦ μ (Metric.thickening δ F)) (𝓝[>] (0 : ℝ)) (𝓝 (μ F)) := by
  convert tendsto_measure_thickening_nhds_measure_closure μ
  exact F_closed.closure_eq.symm

-- TODO: Add similar ones for the closed thickenings (milder assumption, just `𝓝 (0 : ℝ)`).
-- NOTE: There are existing lemmas for these!

#check tendsto_measure_cthickening

/-- If `μ` is a finite measure (on an `OpensMeasurableSpace`), then for any set `E`,
the measures of the closed δ-thickenings of `E` tend to the measure of the closure of `E`
as δ tends to zero. -/
lemma tendsto_measure_cthickening_nhds_measure_closure
    {α : Type _} [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {E : Set α} :
    Tendsto (fun δ ↦ μ (Metric.cthickening δ E)) (𝓝 (0 : ℝ)) (𝓝 (μ (closure E))) := by
  refine tendsto_measure_of_tendsto_indicator (𝓝 (0 : ℝ)) μ isClosed_closure.measurableSet
          (fun δ ↦ (@Metric.isClosed_cthickening _ _ δ E).measurableSet) ?_
  apply eventually_of_forall
  intro x
  have key := tendsto_indicator_cthickening_indicator_closure (fun _ ↦ (1 : ℝ≥0∞)) E
  rw [tendsto_pi_nhds] at key
  exact key x

-- TODO: Deduplicate in Mathlib?

#check tendsto_measure_cthickening_of_isClosed
#check tendsto_measure_cthickening_of_isClosed'

/-- If `μ` is a finite measure (on an `OpensMeasurableSpace`), then for any closed set `F`,
the measures of the closed δ-thickenings of `F` tend to the measure of `F` as δ tends to zero. -/
lemma tendsto_measure_cthickening_of_isClosed''
    {α : Type _} [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {F : Set α} (F_closed : IsClosed F) :
    Tendsto (fun δ ↦ μ (Metric.cthickening δ F)) (𝓝 (0 : ℝ)) (𝓝 (μ F)) := by
  convert tendsto_measure_cthickening_nhds_measure_closure μ
  exact F_closed.closure_eq.symm
 -/









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
