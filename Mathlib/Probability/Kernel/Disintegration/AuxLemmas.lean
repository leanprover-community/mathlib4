import Mathlib.MeasureTheory.Constructions.Polish
import Mathlib.MeasureTheory.Integral.Bochner

open Filter Set MeasureTheory

open scoped Topology ENNReal

variable {α β : Type*} {mα : MeasurableSpace α}

theorem Real.iUnion_Iic_rat : ⋃ r : ℚ, Iic (r : ℝ) = univ := by
  ext1 x
  simp only [mem_iUnion, mem_Iic, mem_univ, iff_true_iff]
  obtain ⟨r, hr⟩ := exists_rat_gt x
  exact ⟨r, hr.le⟩
#align real.Union_Iic_rat Real.iUnion_Iic_rat

theorem Real.iInter_Iic_rat : ⋂ r : ℚ, Iic (r : ℝ) = ∅ := by
  ext1 x
  simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false_iff, not_forall, not_le]
  exact exists_rat_lt x
#align real.Inter_Iic_rat Real.iInter_Iic_rat

lemma measurableSet_tendsto_nhds {β γ ι : Type*} [MeasurableSpace β]
    [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ]
    [hγ : OpensMeasurableSpace γ] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → β → γ} (hf : ∀ i, Measurable (f i)) (c : γ) :
    MeasurableSet { x | Tendsto (fun n ↦ f n x) l (𝓝 c) } := sorry

lemma measurableSet_tendsto_fun {β γ ι : Type*} [MeasurableSpace β]
    [TopologicalSpace γ] [PolishSpace γ] [MeasurableSpace γ]
    [hγ : OpensMeasurableSpace γ] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → β → γ} (hf : ∀ i, Measurable (f i)) {g : β → γ}
    (hg : Measurable g) :
    MeasurableSet { x | Tendsto (fun n ↦ f n x) l (𝓝 (g x)) } := by
  letI := upgradePolishSpace γ
  have : { x | Tendsto (fun n ↦ f n x) l (𝓝 (g x)) }
      = { x | Tendsto (fun n ↦ dist (f n x) (g x)) l (𝓝 0) } := by
    ext x
    simp only [Set.mem_setOf_eq]
    rw [tendsto_iff_dist_tendsto_zero]
  rw [this]
  exact measurableSet_tendsto_nhds (fun n ↦ (hf n).dist hg) 0
