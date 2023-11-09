import Mathlib.Algebra.IndicatorFunction
import Mathlib.Topology.Separation

open Filter Topology

variable {α : Type*} {A : Set α}
variable {ι : Type*} (L : Filter ι) [IsCountablyGenerated L] {As : ι → Set α}

lemma tendsto_indicator_const_iff_forall_eventually' {β : Type*} [Zero β] [TopologicalSpace β]
    (b : β) {B O : Set β} (B_nhd : B ∈ 𝓝 b) (nin_B : 0 ∉ B) (O_nhd : O ∈ 𝓝 0) (nin_O : b ∉ O) :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ ∀ x, ∀ᶠ i in L, (x ∈ As i ↔ x ∈ A) := by
  simp_rw [tendsto_pi_nhds]
  constructor <;> intro h
  · intro x
    specialize h x
    by_cases hx : x ∈ A
    · simp [hx] at h
      filter_upwards [mem_map.mp (h B_nhd)] with i hi
      simp only [Set.mem_preimage, Set.mem_Ioi] at hi
      simp only [show As i x ↔ x ∈ As i by rfl, hx, eq_iff_iff, iff_true]
      by_contra con
      apply nin_B (by simpa [con] using hi)
    · simp [hx] at h
      filter_upwards [mem_map.mp (h O_nhd)] with i hi
      simp only [Set.mem_preimage, Set.mem_Ioi] at hi
      simp only [show As i x ↔ x ∈ As i by rfl, hx, eq_iff_iff, iff_false]
      intro con
      simp [con] at hi
      apply nin_O (by simpa [con] using hi)
  · intro x
    apply Tendsto.congr' (h := tendsto_const_nhds)
    filter_upwards [h x] with i hi
    by_cases x ∈ A <;> · simp [h, hi]

@[simp] lemma tendsto_indicator_const_iff_forall_eventually {β : Type*} [Zero β]
    [TopologicalSpace β] [T1Space β] (b : β) [NeZero b] :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ ∀ x, ∀ᶠ i in L, (x ∈ As i ↔ x ∈ A) := by
  apply tendsto_indicator_const_iff_forall_eventually' _ b (B := {0}ᶜ) (O := {b}ᶜ)
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, NeZero.ne]
  · exact (Set.not_mem_compl_iff).mpr rfl
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, (NeZero.ne b).symm]
  · exact (Set.not_mem_compl_iff).mpr rfl

lemma tendsto_indicator_const_iff_tendsto_pi_pure' {β : Type*} [Zero β] [TopologicalSpace β]
    (b : β) {B O : Set β} (B_nhd : B ∈ 𝓝 b) (nin_B : 0 ∉ B) (O_nhd : O ∈ 𝓝 0) (nin_O : b ∉ O) :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ (Tendsto As L <| Filter.pi (pure <| · ∈ A)) := by
  rw [tendsto_indicator_const_iff_forall_eventually' _ b B_nhd nin_B O_nhd nin_O, tendsto_pi]
  simp_rw [tendsto_pure]
  aesop

lemma tendsto_indicator_const_iff_tendsto_pi_pure {β : Type*} [Zero β] [TopologicalSpace β]
    [T1Space β] (b : β) [NeZero b] :
    Tendsto (fun i ↦ (As i).indicator (fun (_ : α) ↦ b)) L (𝓝 (A.indicator (fun (_ : α) ↦ b)))
      ↔ (Tendsto As L <| Filter.pi (pure <| · ∈ A)) := by
  rw [tendsto_indicator_const_iff_forall_eventually _ b, tendsto_pi]
  simp_rw [tendsto_pure]
  aesop

/- TODO: Update the following

    tendsto_indicator_cthickening_indicator_closure Mathlib.Topology.MetricSpace.ThickenedIndicator
    ∀ {α : Type u_1} [inst : PseudoEMetricSpace α] {β : Type u_2} [inst_1 : Zero β] [inst_2 : TopologicalSpace β] (f : α → β) (E : Set α), Filter.Tendsto (fun δ => Set.indicator (Metric.cthickening δ E) f) (nhds 0) (nhds (Set.indicator (closure E) f))

    tendsto_indicator_thickening_indicator_closure Mathlib.Topology.MetricSpace.ThickenedIndicator
    ∀ {α : Type u_1} [inst : PseudoEMetricSpace α] {β : Type u_2} [inst_1 : Zero β] [inst_2 : TopologicalSpace β] (f : α → β) (E : Set α), Filter.Tendsto (fun δ => Set.indicator (Metric.thickening δ E) f) (nhdsWithin 0 (Set.Ioi 0)) (nhds (Set.indicator (closure E) f))





    MeasureTheory.tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure Mathlib.MeasureTheory.Integral.Indicator
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {A : Set α} {ι : Type u_2} (L : Filter ι) [inst_1 : Filter.IsCountablyGenerated L] {As : ι → Set α} [inst_2 : Filter.NeBot L] (μ : MeasureTheory.Measure α) [inst_3 : MeasureTheory.IsFiniteMeasure μ], (∀ (i : ι), MeasurableSet (As i)) → Filter.Tendsto (fun i => Set.indicator (As i) 1) L (nhds (Set.indicator A 1)) → Filter.Tendsto (fun i => ↑↑μ (As i)) L (nhds (↑↑μ A))

    MeasureTheory.tendsto_measure_of_tendsto_indicator Mathlib.MeasureTheory.Integral.Indicator
    ∀ {α : Type u_1} [inst : MeasurableSpace α] {A : Set α} {ι : Type u_2} (L : Filter ι) [inst_1 : Filter.IsCountablyGenerated L] {As : ι → Set α} [inst_2 : Filter.NeBot L] {μ : MeasureTheory.Measure α}, (∀ (i : ι), MeasurableSet (As i)) → ∀ {B : Set α}, MeasurableSet B → ↑↑μ B ≠ ⊤ → (∀ᶠ (i : ι) in L, As i ⊆ B) → Filter.Tendsto (fun i => Set.indicator (As i) 1) L (nhds (Set.indicator A 1)) → Filter.Tendsto (fun i => ↑↑μ (As i)) L (nhds (↑↑μ A))

    MeasureTheory.tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure Mathlib.MeasureTheory.Integral.Lebesgue
    ∀ {α : Type u_5} [inst : MeasurableSpace α] {A : Set α} {ι : Type u_6} (L : Filter ι) {As : ι → Set α} [inst_1 : Filter.IsCountablyGenerated L] {μ : MeasureTheory.Measure α} [inst_2 : MeasureTheory.IsFiniteMeasure μ], MeasurableSet A → (∀ (i : ι), MeasurableSet (As i)) → (∀ᵐ (x : α) ∂μ, Filter.Tendsto (fun i => Set.indicator (As i) 1 x) L (nhds (Set.indicator A 1 x))) → Filter.Tendsto (fun i => ↑↑μ (As i)) L (nhds (↑↑μ A))

    MeasureTheory.tendsto_measure_of_ae_tendsto_indicator Mathlib.MeasureTheory.Integral.Lebesgue
    ∀ {α : Type u_5} [inst : MeasurableSpace α] {A : Set α} {ι : Type u_6} (L : Filter ι) [inst_1 : Filter.IsCountablyGenerated L] {As : ι → Set α} {μ : MeasureTheory.Measure α}, MeasurableSet A → (∀ (i : ι), MeasurableSet (As i)) → ∀ {B : Set α}, MeasurableSet B → ↑↑μ B ≠ ⊤ → (∀ᶠ (i : ι) in L, As i ⊆ B) → (∀ᵐ (x : α) ∂μ, Filter.Tendsto (fun i => Set.indicator (As i) 1 x) L (nhds (Set.indicator A 1 x))) → Filter.Tendsto (fun i => ↑↑μ (As i)) L (nhds (↑↑μ A))

    measurableSet_of_tendsto_indicator Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
    ∀ {α : Type u_3} [inst : MeasurableSpace α] {A : Set α} {ι : Type u_4} (L : Filter ι) [inst_1 : Filter.IsCountablyGenerated L] {As : ι → Set α} [inst_2 : Filter.NeBot L], (∀ (i : ι), MeasurableSet (As i)) → Filter.Tendsto (fun i => Set.indicator (As i) 1) L (nhds (Set.indicator A 1)) → MeasurableSet A

    nullMeasurableSet_of_tendsto_indicator Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
    ∀ {α : Type u_3} [inst : MeasurableSpace α] {A : Set α} {ι : Type u_4} (L : Filter ι) [inst_1 : Filter.IsCountablyGenerated L] {As : ι → Set α} [inst_2 : Filter.NeBot L] {μ : MeasureTheory.Measure α}, (∀ (i : ι), MeasureTheory.NullMeasurableSet (As i)) → (∀ᵐ (x : α) ∂μ, Filter.Tendsto (fun i => Set.indicator (As i) 1 x) L (nhds (Set.indicator A 1 x))) → MeasureTheory.NullMeasurableSet A

-/
