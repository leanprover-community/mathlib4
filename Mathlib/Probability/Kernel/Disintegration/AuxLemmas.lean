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

lemma integral_tendsto_of_tendsto_of_monotone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  let f' := fun n x ↦ f n x - f 0 x
  have hf'_nonneg : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f' n x := by
    filter_upwards [h_mono] with a ha n
    simp [ha (zero_le n)]
  have hf'_meas : ∀ n, Integrable (f' n) μ := fun n ↦ (hf n).sub (hf 0)
  suffices Tendsto (fun n ↦ ∫ x, f' n x ∂μ) atTop (𝓝 (∫ x, (F - f 0) x ∂μ)) by
    rw [integral_sub' hF (hf 0)] at this
    have h_sub : ∀ n, ∫ x, f' n x ∂μ = ∫ x, f n x ∂μ - ∫ x, f 0 x ∂μ := by
      intro n
      simp only
      rw [integral_sub (hf n) (hf 0)]
    simp_rw [h_sub] at this
    have h1 : (fun n ↦ ∫ x, f n x ∂μ)
        = fun n ↦ (∫ x, f n x ∂μ - ∫ x, f 0 x ∂μ) + ∫ x, f 0 x ∂μ := by ext n; abel
    have h2 : ∫ x, F x ∂μ = (∫ x, F x ∂μ - ∫ x, f 0 x ∂μ) + ∫ x, f 0 x ∂μ := by abel
    rw [h1, h2]
    exact this.add tendsto_const_nhds
  have hF_ge : 0 ≤ᵐ[μ] fun x ↦ (F - f 0) x := by
    filter_upwards [h_tendsto, h_mono] with x hx_tendsto hx_mono
    simp only [Pi.zero_apply, Pi.sub_apply, sub_nonneg]
    exact ge_of_tendsto' hx_tendsto (fun n ↦ hx_mono (zero_le _))
  rw [ae_all_iff] at hf'_nonneg
  simp_rw [integral_eq_lintegral_of_nonneg_ae (hf'_nonneg _) (hf'_meas _).1]
  rw [integral_eq_lintegral_of_nonneg_ae hF_ge (hF.1.sub (hf 0).1)]
  have h_cont := ENNReal.continuousOn_toReal.continuousAt
    (x := ∫⁻ a, ENNReal.ofReal ((F - f 0) a) ∂μ) ?_
  swap
  · rw [mem_nhds_iff]
    refine ⟨Iio (∫⁻ a, ENNReal.ofReal ((F - f 0) a) ∂μ + 1), ?_, isOpen_Iio, ?_⟩
    · intro x
      simp only [Pi.sub_apply, mem_Iio, ne_eq, mem_setOf_eq]
      exact ne_top_of_lt
    · simp only [Pi.sub_apply, mem_Iio]
      refine ENNReal.lt_add_right ?_ one_ne_zero
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · exact ENNReal.ofReal_ne_top
      · exact hF.sub (hf 0)
      · exact hF_ge
  refine h_cont.tendsto.comp ?_
  refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
  · exact fun n ↦ ((hf n).sub (hf 0)).aemeasurable.ennreal_ofReal
  · filter_upwards [h_mono] with x hx
    intro n m hnm
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [tsub_le_iff_right, sub_add_cancel]
    exact hx hnm
  · filter_upwards [h_tendsto] with x hx
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    simp only [Pi.sub_apply]
    exact Tendsto.sub hx tendsto_const_nhds

lemma integral_tendsto_of_tendsto_of_antitone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : ∀ᵐ x ∂μ, Antitone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  suffices Tendsto (fun n ↦ ∫ x, -f n x ∂μ) atTop (𝓝 (∫ x, -F x ∂μ)) by
    suffices Tendsto (fun n ↦ ∫ x, - -f n x ∂μ) atTop (𝓝 (∫ x, - -F x ∂μ)) by
      simp_rw [neg_neg] at this
      exact this
    convert this.neg <;> rw [integral_neg]
  refine integral_tendsto_of_tendsto_of_monotone (fun n ↦ (hf n).neg) hF.neg ?_ ?_
  · filter_upwards [h_mono] with x hx
    intro n m hnm
    simp only [neg_le_neg_iff]
    exact hx hnm
  · filter_upwards [h_tendsto] with x hx
    exact hx.neg

lemma tendsto_nat_ceil_atTop {α : Type*} [LinearOrderedSemiring α] [FloorSemiring α] :
    Tendsto (fun x : α ↦ ⌈x⌉₊) atTop atTop := by
  refine Nat.ceil_mono.tendsto_atTop_atTop (fun x ↦ ⟨x, ?_⟩)
  simp only [Nat.ceil_natCast, le_refl]

lemma isCoboundedUnder_le_of_eventually_le {ι α : Type*} [Preorder α] (l : Filter ι) [NeBot l]
    {f : ι → α} {x : α} (hf : ∀ᶠ i in l, x ≤ f i) :
    IsCoboundedUnder (· ≤ ·) l f :=
  IsBoundedUnder.isCoboundedUnder_le ⟨x, hf⟩

lemma isCoboundedUnder_le_of_le {ι α : Type*} [Preorder α] (l : Filter ι) [NeBot l] {f : ι → α}
    {x : α} (hf : ∀ i, x ≤ f i) :
    IsCoboundedUnder (· ≤ ·) l f :=
  isCoboundedUnder_le_of_eventually_le l (eventually_of_forall hf)
