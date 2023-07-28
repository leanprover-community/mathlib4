import Mathlib
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable




section TendstoMeasureOfTendstoIndicator

open MeasureTheory Set Filter Topology ENNReal NNReal BigOperators

lemma measurable_indicator_const_iff' [MeasurableSpace α] (A : Set α) [Zero β] [MeasurableSpace β]
  (h0 : MeasurableSet ({0} : Set β)) (b : β) :
    Measurable (A.indicator (fun _ ↦ b)) ↔ (b = 0 ∨ MeasurableSet A) := by
  constructor <;> intro h
  · by_cases hb : b = 0 <;> simp only [hb, true_or, false_or]
    convert h h0.compl
    ext a
    simp [hb]
  · by_cases hb : b = 0
    · simp only [hb, indicator_zero, measurable_const]
    · have A_mble : MeasurableSet A := by simpa only [hb, false_or] using h
      intro B _
      rcases indicator_const_preimage A B b with ⟨hB⟩ | ⟨hB | ⟨hB | hB⟩⟩
      · simp only [hB, MeasurableSet.univ]
      · simp only [hB, A_mble]
      · simp only [hB, MeasurableSet.compl_iff, A_mble]
      · simp only [mem_singleton_iff] at hB
        simp only [hB, MeasurableSet.empty]

lemma measurable_indicator_const_iff [MeasurableSpace α] (A : Set α) [Zero β] [MeasurableSpace β]
  [MeasurableSingletonClass β] (b : β) :
    Measurable (A.indicator (fun _ ↦ b)) ↔ (b = 0 ∨ MeasurableSet A) :=
  measurable_indicator_const_iff' A (MeasurableSet.singleton 0) b

lemma measurableSet_of_tendsto_indicator {α ι : Type _}
    (L : Filter ι) [IsCountablyGenerated L] [NeBot L]
    [MeasurableSpace α] {A : Set α} {As : ι → Set α} (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞))))) :
    MeasurableSet A := by
  have obs := measurable_indicator_const_iff A (1 : ℝ≥0∞)
  simp only [one_ne_zero, false_or] at obs
  rw [←obs]
  have := @measurable_of_tendsto_ennreal' α _ ι (fun i x ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
    (A.indicator (fun _ ↦ (1 : ℝ≥0∞))) L _ _
  apply this
  · intro i
    simp only [measurable_indicator_const_iff, one_ne_zero, As_mble i, or_true]
  · simpa [tendsto_pi_nhds] using h_lim

/-- If the indicators of measurable sets `As i` tend pointwise almost everywhere to the indicator
of a measurable set `A` (along a countably generated filter), then the measures of `As i` tend to
the measure of `A`. -/
lemma tendsto_measure_of_tendsto_indicator'
    {α ι : Type _} (L : Filter ι) [IsCountablyGenerated L]
    [MeasurableSpace α] (μ : Measure α) {A : Set α} (A_mble : MeasurableSet A)
    {As : ι → Set α} (As_mble : ∀ i, MeasurableSet (As i))
    {B : Set α} (B_mble : MeasurableSet B) (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  simp_rw [← MeasureTheory.lintegral_indicator_one A_mble, ← MeasureTheory.lintegral_indicator_one (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (B.indicator (fun _ ↦ (1 : ℝ≥0∞)))
          (eventually_of_forall ?_) ?_ ?_ h_lim
  · exact fun i ↦ Measurable.indicator measurable_const (As_mble i)
  · filter_upwards [As_le_B] with i hi
    apply eventually_of_forall
    intro x
    exact indicator_le_indicator_of_subset hi (by simp) x
  · rwa [← lintegral_indicator_one B_mble] at B_finmeas

/-- If `μ` is a finite measure and the indicators of measurable sets `As i` tend pointwise
almost everywhere to the indicator of a measurable set `A` (along a countably generated filter),
then the measures `μ (As i)` tend to the measure `μ A`. -/
lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure'
    {α ι : Type _} (L : Filter ι) [IsCountablyGenerated L]
    [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] {A : Set α} (A_mble : MeasurableSet A)
    {As : ι → Set α} (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) :=
  tendsto_measure_of_tendsto_indicator' L μ A_mble As_mble MeasurableSet.univ
    (measure_ne_top μ univ) (eventually_of_forall (fun i ↦ subset_univ (As i))) h_lim

/-- If the indicators of measurable sets `As i` tend pointwise to the indicator of a set `A`
(along a countably generated filter), then the measures of `As i` tend to the measure of `A`. -/
lemma tendsto_measure_of_tendsto_indicator
    {α ι : Type _} (L : Filter ι) [IsCountablyGenerated L] [NeBot L]
    [MeasurableSpace α] (μ : Measure α) {A : Set α}
    {As : ι → Set α} (As_mble : ∀ i, MeasurableSet (As i))
    {B : Set α} (B_mble : MeasurableSet B) (B_finmeas : μ B ≠ ∞) (As_le_B : ∀ᶠ i in L, As i ⊆ B)
    (h_lim : Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞))))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_tendsto_indicator' L μ ?_ As_mble B_mble B_finmeas As_le_B
  · apply eventually_of_forall
    simpa only [tendsto_pi_nhds] using h_lim
  · exact @measurableSet_of_tendsto_indicator α ι L _ _ _ A As As_mble h_lim

/-- If `μ` is a finite measure and the indicators of measurable sets `As i` tend pointwise to
the indicator of a set `A` (along a countably generated filter), then the measures `μ (As i)`
tend to the measure `μ A`. -/
lemma tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
    {α ι : Type _} (L : Filter ι) [IsCountablyGenerated L] [NeBot L]
    [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] {A : Set α}
    {As : ι → Set α} (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)))
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞))))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  apply tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure' L μ ?_ As_mble
  · apply eventually_of_forall
    simpa only [tendsto_pi_nhds] using h_lim
  · exact @measurableSet_of_tendsto_indicator α ι L _ _ _ A As As_mble h_lim

#find_home tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure

end TendstoMeasureOfTendstoIndicator
