import Mathlib.Analysis.BoxIntegral.Integrability

section Set.indicator

variable {α β : Type*} [One β] {f : α → β} {s : Set α}

namespace Set

@[to_additive]
theorem eqOn_mulIndicator' : EqOn (mulIndicator s f) (fun _ ↦ 1) sᶜ :=
  fun _ hx => mulIndicator_of_not_mem hx f

open Topology

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [One β] {f : α → β} {s : Set α}
  (hf : ContinuousOn f s)

@[to_additive]
theorem continuous_mulIndicator_of_not_mem_frontier {x : α} (hx : x ∉ frontier s) :
    ContinuousAt (s.mulIndicator f) x := by
  classical
  rw [← Set.not_mem_compl_iff, Set.not_not_mem, compl_frontier_eq_union_interior] at hx
  cases hx with
  | inl h =>
      have hs : s ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp h
      exact ContinuousAt.congr (hf.continuousAt hs) <|
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨s, hs, Set.eqOn_mulIndicator.symm⟩
  | inr h =>
      exact ContinuousAt.congr continuousAt_const <|
        Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨sᶜ, mem_interior_iff_mem_nhds.mp h, eqOn_mulIndicator'.symm⟩

end Set

end Set.indicator

open BoxIntegral Topology EMetric BigOperators

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {I J : Box ι}

local notation "ℝⁿ" => ι → ℝ

/-- The oscillation of `f` at `x`. -/
noncomputable def oscillation (f : ℝⁿ → E) (x : ℝⁿ) : ENNReal :=
  ⨅ S ∈ (𝓝 x).map f, diam S

/-- The oscillation of `f` at `x` is 0 whenever `f` is continuous at `x`. -/
theorem oscillation_zero_of_continuousAt {f : ℝⁿ → E} {x : ℝⁿ} (hf : ContinuousAt f x) :
    oscillation f x = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_) (zero_le _)
  rw [zero_add]
  have : ball (f x) (ε / 2) ∈ (𝓝 x).map f := hf <| ball_mem_nhds _ (by simp [ne_of_gt hε])
  refine (biInf_le diam this).trans (le_of_le_of_eq diam_ball ?_)
  refine (ENNReal.mul_div_cancel' ?_ ?_) <;> norm_num

/-- If `oscillation f x < ε` at every `x` in a compact set `K`, then there exists `δ > 0` such
that the oscillation of `f` on `Metric.ball x δ` is less than `ε` for every `x` in `K`. -/
theorem uniform_oscillation_of_compact {K : Set ℝⁿ} (comp : IsCompact K) (f : ℝⁿ → E)
    (ε : ENNReal) (hK : ∀ x ∈ K, oscillation f x < ε) :
    ∃ δ > 0, ∀ x ∈ K, diam (f '' (Metric.ball x δ)) ≤ ε := by
  let S := fun r ↦ { x : ℝⁿ | ∃ (a : ℝ), (a > r ∧ diam (f '' (Metric.ball x a)) ≤ ε) }
  have S_open : ∀ r > 0, IsOpen (S r) := by
    intro r _
    rw [isOpen_iff_nhds]
    rintro x ⟨a, ar, ha⟩ t ht
    rw [Metric.mem_nhds_iff]
    use (a - r) / 2, by simp [ar]
    intro y hy
    apply ht
    use a - (a - r) / 2, by linarith
    refine le_trans (diam_mono (Set.image_mono fun z hz ↦ ?_)) ha
    rw [Metric.mem_ball] at *
    linarith [dist_triangle z y x]
  have S_cover : K ⊆ ⋃ r > 0, S r := by
    intro x hx
    have : oscillation f x < ε := hK x hx
    simp only [oscillation, Filter.mem_map, iInf_lt_iff] at this
    obtain ⟨n, hn₁, hn₂⟩ := this
    obtain ⟨r, r0, hr⟩ := Metric.mem_nhds_iff.1 hn₁
    use (S (r / 2)), ⟨r / 2, by simp [r0]⟩, r, div_two_lt_of_pos r0
    exact le_trans (diam_mono (Set.image_subset_iff.2 hr)) (le_of_lt hn₂)
  have S_antitone : ∀ (r₁ r₂ : ℝ), r₁ ≤ r₂ → S r₂ ⊆ S r₁ :=
    fun r₁ r₂ hr x ⟨a, ar₂, ha⟩ ↦ ⟨a, lt_of_le_of_lt hr ar₂, ha⟩
  have : ∃ r > 0, K ⊆ S r := by
    obtain ⟨T, Tb, Tfin, hT⟩ := comp.elim_finite_subcover_image S_open S_cover
    by_cases T_nonempty : T.Nonempty
    · use Tfin.isWF.min T_nonempty, Tb (Tfin.isWF.min_mem T_nonempty)
      intro x hx
      obtain ⟨r, hr⟩ := Set.mem_iUnion.1 (hT hx)
      simp only [Set.mem_iUnion, exists_prop] at hr
      exact (S_antitone _ r (Set.IsWF.min_le Tfin.isWF T_nonempty hr.1)) hr.2
    · rw [Set.not_nonempty_iff_eq_empty] at T_nonempty
      use 1, one_pos, subset_trans hT (by simp [T_nonempty])
  obtain ⟨δ, δ0, hδ⟩ := this
  use δ, δ0
  intro x xK
  obtain ⟨a, δa, ha⟩ := hδ xK
  exact le_trans (diam_mono (Set.image_mono (Metric.ball_subset_ball (le_of_lt δa)))) ha

open MeasureTheory Prepartition Set Classical

/-- A function that is bounded and a.e. continuous on a box `I` is integrable on `I`. -/
theorem integrable_of_bounded_and_ae_continuous (l : IntegrationParams) [CompleteSpace E]
    {I : Box ι} {f : ℝⁿ → E} (hb : ∃ C : ℝ, ∀ x ∈ Box.Icc I, ‖f x‖ ≤ C) (μ : Measure ℝⁿ)
    [IsLocallyFiniteMeasure μ] (hc : ∀ᵐ x ∂μ, ContinuousAt f x) :
    Integrable I l f μ.toBoxAdditive.toSMul := by
  refine' integrable_iff_cauchy_basis.2 fun ε ε0 ↦ _
  rcases exists_pos_mul_lt ε0 (2 * μ.toBoxAdditive I) with ⟨ε₁, ε₁0, hε₁⟩
  rcases hb with ⟨C, hC⟩
  by_cases C0 : C ≥ 0; swap
  · obtain ⟨x, hx⟩ := BoxIntegral.Box.nonempty_coe I
    exact False.elim <| C0 <| le_trans (norm_nonneg (f x)) <| hC x (Box.coe_subset_Icc hx)
  rcases exists_pos_mul_lt ε0 (4 * C) with ⟨ε₂, ε₂0, hε₂⟩
  have ε₂0': ENNReal.ofReal ε₂ ≠ 0 := fun h ↦ not_le_of_gt ε₂0 (ENNReal.ofReal_eq_zero.1 h)
  let D := { x ∈ Box.Icc I | ¬ ContinuousAt f x }
  have μD : μ D = 0 := by
    obtain ⟨v, v_ae, hv⟩ := Filter.eventually_iff_exists_mem.1 hc
    exact eq_of_le_of_not_lt (le_of_le_of_eq (μ.mono <| fun x hx xv ↦ hx.2 (hv x xv))
                                (mem_ae_iff.1 v_ae)) ENNReal.not_lt_zero
  obtain ⟨U, UD, Uopen, hU⟩ := Set.exists_isOpen_lt_add D (show μ D ≠ ⊤ by simp [μD]) ε₂0'
  rw [μD, zero_add] at hU
  have comp : IsCompact (Box.Icc I \ U) :=
    I.isCompact_Icc.of_isClosed_subset (I.isCompact_Icc.isClosed.sdiff Uopen) (Set.diff_subset _ U)
  have : ∀ x ∈ (Box.Icc I \ U), oscillation f x < (ENNReal.ofReal ε₁) := by
    intro x hx
    suffices oscillation f x = 0 by rw [this]; exact ENNReal.ofReal_pos.2 ε₁0
    apply oscillation_zero_of_continuousAt
    simpa [D, hx.1] using hx.2 ∘ (fun a ↦ UD a)
  obtain ⟨r, r0, hr⟩ := uniform_oscillation_of_compact comp f (ENNReal.ofReal ε₁) this
  refine' ⟨fun _ _ ↦ ⟨r / 2, half_pos r0⟩, fun _ _ _ ↦ rfl, fun c₁ c₂ π₁ π₂ h₁ h₁p h₂ h₂p ↦ _⟩
  simp only [dist_eq_norm, integralSum_sub_partitions _ _ h₁p h₂p, BoxAdditiveMap.toSMul_apply,
    ← smul_sub]
  set B := (π₁.toPrepartition ⊓ π₂.toPrepartition).boxes
  let p : Box ι → Prop := fun J ↦ (J.toSet ⊆ U)
  rw [← Finset.sum_sdiff (Finset.filter_subset p B), ← add_halves ε]
  have μI_lt_top := lt_of_le_of_lt (μ.mono I.coe_subset_Icc) I.isCompact_Icc.measure_lt_top
  have μJ_ne_top : ∀ J ∈ B, μ J ≠ ⊤ := fun J hJ ↦ lt_top_iff_ne_top.1 <| lt_of_le_of_lt
                      (μ.mono (Prepartition.le_of_mem' _ J hJ)) μI_lt_top
  have union : ∀ S ⊆ B, ⋃ J ∈ S, J.toSet ⊆ I.toSet :=
    fun S hS ↦ iUnion_subset_iff.2 (fun J ↦ iUnion_subset_iff.2 fun hJ ↦ le_of_mem' _ J (hS hJ))
  apply le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · have : ∀ J ∈ B \ B.filter p, ‖μ.toBoxAdditive J •
      (f ((π₁.infPrepartition π₂.toPrepartition).tag J) -
      f ((π₂.infPrepartition π₁.toPrepartition).tag J))‖ ≤ μ.toBoxAdditive J * ε₁ := by
      intro J hJ
      rw [norm_smul, μ.toBoxAdditive_apply, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
      have : ∃ x ∈ J, x ∉ U := by
        rw [Finset.mem_sdiff, Finset.mem_filter, not_and] at hJ
        simpa only [p, Set.not_subset] using hJ.2 hJ.1
      obtain ⟨x, xJ, xnU⟩ := this
      have hx : x ∈ Box.Icc I \ U :=
        ⟨Box.coe_subset_Icc <| (le_of_mem' _ J (Finset.mem_sdiff.1 hJ).1) xJ, xnU⟩
      have JB : J ∈ B := (Finset.mem_sdiff.1 hJ).1
      have hy : (π₁.infPrepartition π₂.toPrepartition).tag J ∈ Metric.ball x r :=
        Metric.closedBall_subset_ball (div_two_lt_of_pos r0) (Metric.mem_closedBall_comm.1 <|
            h₁.isSubordinate.infPrepartition π₂.toPrepartition J JB (Box.coe_subset_Icc xJ))
      have hz : (π₂.infPrepartition π₁.toPrepartition).tag J ∈ Metric.ball x r := by
        refine Metric.closedBall_subset_ball (div_two_lt_of_pos r0) (Metric.mem_closedBall_comm.1 <|
            h₂.isSubordinate.infPrepartition π₁.toPrepartition J ?_ (Box.coe_subset_Icc xJ))
        rwa [BoxIntegral.TaggedPrepartition.mem_infPrepartition_comm]
      simpa only [edist_le_ofReal (le_of_lt ε₁0), dist_eq_norm, (Finset.mem_sdiff.1 hJ).1] using
        le_trans (edist_le_diam_of_mem (mem_image_of_mem f hy) (mem_image_of_mem f hz)) (hr x hx)
    refine (norm_sum_le _ _).trans <| (Finset.sum_le_sum this).trans ?_
    rw [← Finset.sum_mul]
    trans μ.toBoxAdditive I * ε₁; swap
    · rw [le_div_iff' two_pos, ← mul_assoc]
      exact le_of_lt hε₁
    · simp_rw [mul_le_mul_right ε₁0, Measure.toBoxAdditive_apply]
      refine le_trans ?_ <| ENNReal.toReal_mono (lt_top_iff_ne_top.1 μI_lt_top) <| μ.mono <|
          union _ (Finset.sdiff_subset B (B.filter p))
      rw [← ENNReal.toReal_sum, ← Finset.tsum_subtype]; swap
      · exact fun J hJ ↦ μJ_ne_top J (Finset.mem_sdiff.1 hJ).1
      apply (ENNReal.toReal_mono <| ne_of_lt <| lt_of_le_of_lt (μ.mono <|
        union _ (Finset.sdiff_subset B (B.filter p))) μI_lt_top) <| le_of_eq (Eq.symm ?_)
      refine measure_biUnion (Finset.countable_toSet _) ?_ (fun J _ ↦ J.measurableSet_coe)
      intro J hJ J' hJ' hJJ'
      exact pairwiseDisjoint _ (Finset.mem_sdiff.1 hJ).1 (Finset.mem_sdiff.1 hJ').1 hJJ'
  · have : ∀ J ∈ B.filter p, ‖μ.toBoxAdditive J • (f ((π₁.infPrepartition π₂.toPrepartition).tag J) -
        f ((π₂.infPrepartition π₁.toPrepartition).tag J))‖ ≤ μ.toBoxAdditive J * (2 * C) := by
      intro J _
      rw [norm_smul, μ.toBoxAdditive_apply, Real.norm_of_nonneg ENNReal.toReal_nonneg, two_mul]
      apply mul_le_mul_of_nonneg_left (le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)) (by simp) <;>
        exact hC _ (TaggedPrepartition.tag_mem_Icc _ J)
    apply le_trans (norm_sum_le_of_le _ this)
    simp_rw [← Finset.sum_mul, Measure.toBoxAdditive_apply]
    rw [← ENNReal.toReal_sum (fun J hJ ↦ μJ_ne_top J (B.filter_subset p hJ))]
    have : (∑ a in B.filter p, μ a).toReal ≤ ε₂ := by
      rw [← ENNReal.toReal_ofReal (le_of_lt ε₂0)]
      refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ( le_of_lt <| lt_of_le_of_lt ?_ hU)
      trans μ (⋃ J ∈ B.filter p, J)
      · apply le_of_eq
        rw [← Finset.tsum_subtype]
        apply (measure_biUnion (B.filter p).countable_toSet ?_ (fun J _ ↦ J.measurableSet_coe)).symm
        intro J hJ J' hJ' hJJ'
        exact pairwiseDisjoint _ (B.filter_subset p hJ) (B.filter_subset p hJ') hJJ'
      · apply μ.mono
        simp_rw [iUnion_subset_iff]
        exact fun J hJ ↦ (Finset.mem_filter.1 hJ).2
    apply le_trans <| mul_le_mul_of_nonneg_right this <| (mul_nonneg_iff_of_pos_left two_pos).2 C0
    linarith

/-- If `f : ℝⁿ → E` is bounded and continuous a.e. on a rectangular box `I`, then it is Box
integrable on `I` w.r.t. a locally finite measure `μ` with the same integral. -/
theorem hasBoxIntegral_of_bounded_and_ae_continuous [CompleteSpace E] {f : (ι → ℝ) → E}
    (μ : Measure (ι → ℝ)) [IsLocallyFiniteMeasure μ] {I : Box ι}
    (hb : ∃ C : ℝ, ∀ x ∈ Box.Icc I, ‖f x‖ ≤ C) (hc : ∀ᵐ x ∂μ, ContinuousAt f x)
    (l : IntegrationParams) :
    HasIntegral I l f μ.toBoxAdditive.toSMul (∫ x in I, f x ∂μ) := by
  obtain ⟨y, hy⟩ := integrable_of_bounded_and_ae_continuous l hb μ hc
  convert hy
  have : IntegrableOn f I μ := by
    sorry
  exact HasIntegral.unique (IntegrableOn.hasBoxIntegral this ⊥ rfl) (HasIntegral.mono hy bot_le)
