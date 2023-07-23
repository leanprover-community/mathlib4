import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open MeasureTheory Set Filter BoundedContinuousFunction Topology ENNReal NNReal BigOperators

section minor_updates

open Metric

#check tendsto_measure_cthickening
#check tendsto_measure_cthickening_of_isClosed

-- NOTE: The only difference to existing lemmas is:
--  `[PseudoMetricSpace α]` -> `[PseudoEMetricSpace α]`
-- TODO: Just PR the obvious generalization.
variable [PseudoEMetricSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]

/-- If a set has a closed thickening with finite measure, then the measure of its `r`-closed
thickenings converges to the measure of its closure as `r` tends to `0`. -/
theorem tendsto_measure_cthickening'  {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (cthickening R s) ≠ ∞) :
    Tendsto (fun r => μ (cthickening r s)) (𝓝 0) (𝓝 (μ (closure s))) := by
  have A : Tendsto (fun r => μ (cthickening r s)) (𝓝[Ioi 0] 0) (𝓝 (μ (closure s))) := by
    rw [closure_eq_iInter_cthickening]
    exact
      tendsto_measure_biInter_gt (fun r _ => isClosed_cthickening.measurableSet)
        (fun i j _ ij => cthickening_mono ij _) hs
  have B : Tendsto (fun r => μ (cthickening r s)) (𝓝[Iic 0] 0) (𝓝 (μ (closure s))) := by
    apply Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin (α := ℝ)] with _ hr
    rw [cthickening_of_nonpos hr]
  convert B.sup A
  exact (nhds_left_sup_nhds_right' 0).symm

/-- If a closed set has a closed thickening with finite measure, then the measure of its `r`-closed
thickenings converges to its measure as `r` tends to `0`. -/
theorem tendsto_measure_cthickening_of_isClosed' {μ : Measure α} {s : Set α}
    (hs : ∃ R > 0, μ (cthickening R s) ≠ ∞) (h's : IsClosed s) :
    Tendsto (fun r => μ (cthickening r s)) (𝓝 0) (𝓝 (μ s)) := by
  convert tendsto_measure_cthickening' hs
  exact h's.closure_eq.symm

end minor_updates



section borel_imp

variable (α : Type _) [MeasurableSpace α]

#check Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top
#check Measure.countable_meas_pos_of_disjoint_iUnion
#check Metric.frontier_thickening_disjoint
#check Metric.frontier_thickening_disjoint
#check exists_null_frontier_thickening
#check exists_null_frontiers_thickening

lemma ProbabilityMeasure.coe_null_iff (μ : ProbabilityMeasure α) (E : Set α) :
    (μ : Measure α) E = 0 ↔ μ E = 0 := by
  constructor <;> intro h
  · simp only [h, zero_toNNReal]
  · simpa only [toNNReal_eq_zero_iff, (measure_lt_top (↑μ) E).ne, or_false] using h

variable [TopologicalSpace α]

-- NOTE: Missing?
@[to_additive] lemma _root_.set.mulIndicator_iInter_apply {α ι M}
    [Nonempty ι] [CompleteLattice M] [One M]
    (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M) (x : α) :
    mulIndicator (⋂ i, s i) f x = ⨅ i, mulIndicator (s i) f x := by
  by_cases hx : x ∈ ⋂ i, s i
  · rw [mulIndicator_of_mem hx]
    rw [mem_iInter] at hx
    refine le_antisymm ?_ ?_
    · exact le_iInf (fun j ↦ by simp only [mulIndicator_of_mem (hx j), le_refl])
    · simp only [mulIndicator_of_mem (hx _), ciInf_const, le_refl]
  · rw [mulIndicator_of_not_mem hx]
    simp only [mem_iInter, not_exists, not_forall] at hx
    rcases hx with ⟨j, hj⟩
    refine le_antisymm ?_ ?_
    · simp only [← h1, le_iInf_iff, bot_le, forall_const]
    · simpa [mulIndicator_of_not_mem hj] using (iInf_le (fun i ↦ (s i).mulIndicator f) j) x

#check set.indicator_iInter_apply

-- TODO: avoid this?
lemma lintegral_indicator_one {α : Type _} [MeasurableSpace α] (μ : Measure α)
    {s : Set α} (s_mble : MeasurableSet s) :
    ∫⁻ x, (s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x) ∂μ = μ s := by
  simp [lintegral_indicator _ s_mble]

-- NOTE: Missing?
lemma tendsto_measure_of_tendsto_indicator
    {α ι : Type _} (L : Filter ι) [IsCountablyGenerated L]
    [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] {A : Set α} (A_mble : MeasurableSet A)
    {As : ι → Set α} (As_mble : ∀ i, MeasurableSet (As i))
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ (As i).indicator (fun _ ↦ (1 : ℝ≥0∞)) x)
      L (𝓝 (A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x))) :
    Tendsto (fun i ↦ μ (As i)) L (𝓝 (μ A)) := by
  simp_rw [← lintegral_indicator_one μ A_mble, ← lintegral_indicator_one μ (As_mble _)]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ≥0∞))
          (eventually_of_forall ?_) (eventually_of_forall ?_) ?_ h_lim
  · exact fun i ↦ Measurable.indicator measurable_const (As_mble i)
  · exact fun i ↦ eventually_of_forall (fun x ↦ indicator_apply_le (fun _ ↦ le_refl _))
  · rw [lintegral_one]
    exact (measure_lt_top μ univ).ne

lemma tendsto_measure_thickening_nhds_measure_closure
    {α : Type _} [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {E : Set α} :
    Tendsto (fun δ ↦ μ (Metric.thickening δ E)) (𝓝[>] (0 : ℝ)) (𝓝 (μ (closure E))) := by
  refine tendsto_measure_of_tendsto_indicator (𝓝[>] (0 : ℝ)) μ isClosed_closure.measurableSet
          (fun δ ↦ (@Metric.isOpen_thickening _ _ δ E).measurableSet) ?_
  apply eventually_of_forall
  intro x
  have key := tendsto_indicator_thickening_indicator_closure (fun _ ↦ (1 : ℝ≥0∞)) E
  rw [tendsto_pi_nhds] at key
  exact key x

lemma tendsto_measure_thickening_of_isClosed
    {α : Type _} [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {F : Set α} (F_closed : IsClosed F) :
    Tendsto (fun δ ↦ μ (Metric.thickening δ F)) (𝓝[>] (0 : ℝ)) (𝓝 (μ F)) := by
  convert tendsto_measure_thickening_nhds_measure_closure μ
  exact F_closed.closure_eq.symm

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
  have keyB := @tendsto_measure_cthickening_of_isClosed' α _ _ _ μ F
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



/-
begin
  have ex := exists_null_frontiers_thickening' α μ F,
  let rs := classical.some ex,
  have rs_lim : tendsto rs at_top (𝓝[>] 0), from (classical.some_spec ex).1,
  have rs_pos : ∀ n, 0 < rs n, by sorry, --from λ n, ((classical.some_spec ex).2 n).1,
  have rs_null : ∀ n, (μ : measure α) (frontier (metric.thickening (rs n) F)) = 0,
    from λ n, ((classical.some_spec ex).2 n),
  have Fthicks_open : ∀ n, is_open (metric.thickening (rs n) F),
    from λ n, metric.is_open_thickening,
  have key := λ (n : ℕ), h (Fthicks_open n).measurable_set
                  (by { specialize rs_null n, rwa probability_measure.coe_null_iff at rs_null, }),
  -- limsupᵢ (μᵢ F) ≤ limsupᵢ (μᵢ Fδ) = limᵢ (μᵢ Fδ) = μ Fδ ≤ μ F + ε
  apply ennreal.le_of_forall_pos_le_add,
  intros ε ε_pos μF_finite,
/-   have aux' := λ n, λ i, @measure_mono _ _ (μs i : measure α) _ _ (metric.self_subset_thickening (rs_pos n) F),
  have aux : ∀ n,
      (λ i, (μs i : measure α) F) ≤ᶠ[L] (λ i, (μs i : measure α) (metric.thickening (rs n) F)),
    from λ n, eventually_of_forall (aux' n),
  have := λ n, limsup_le_limsup (aux n),
 -/
  --have := @measure_mono _ _ (μ : measure α),

  have keyB := tendsto_measure_thickening_of_is_closed (μ : measure α) F_closed,
  have nhd : Iio ((μ : measure α) F + ε) ∈ 𝓝 ((μ : measure α) F),
  { apply Iio_mem_nhds,
    simpa only [add_zero] using ennreal.add_lt_add_left μF_finite.ne (ennreal.coe_pos.mpr ε_pos), },
  specialize rs_lim (keyB nhd),
  simp only [mem_map, mem_at_top_sets, ge_iff_le, mem_preimage, mem_Iio] at rs_lim,
  rcases rs_lim with ⟨m, hm⟩,
  have whee := hm m rfl.le,
  have aux' := λ i, @measure_mono _ _ (μs i : measure α) _ _ (metric.self_subset_thickening (rs_pos m) F),
  --refine (limsup_le_limsup (eventually_of_forall aux')).trans _,
  have aux : (λ i, (μs i : measure α) F)
              ≤ᶠ[L] (λ i, (μs i : measure α) (metric.thickening (rs m) F)),
    from eventually_of_forall aux',
  refine (limsup_le_limsup aux).trans _,
  --have := tendsto.limsup_eq,
  have := key m, -- Should do `⇑↑(μs i)` instead of `↑(μs i)`. :(
  have := tendsto.limsup_eq (key m),

  --rw this,

  -- specialize keyB nhd,
  -- simp only [mem_map] at keyB,


  --rcases mem_nhds_within_Ioi_iff_exists_Ioo_subset.mp keyB with ⟨δ₀, ⟨δ₀_pos, hδ₀⟩⟩,
  --rcases nonempty_Ioo.mpr δ₀_pos with ⟨δ', hδ'⟩,

  --have := tendsto_mono,
  --have := finite_measure.tendsto
  --have := le_of_forall_pos
  sorry,
end
 -/

end borel_imp

/-
import measure_theory.measure.portmanteau
import measure_theory.measure.lebesgue

noncomputable theory
open measure_theory
open set
open filter
open bounded_continuous_function
open_locale topological_space ennreal nnreal bounded_continuous_function big_operators

section borel_imp

variables (α : Type*) [measurable_space α]

#check measure.countable_meas_pos_of_disjoint_of_meas_Union_ne_top
#check measure.countable_meas_pos_of_disjoint_Union

#check metric.frontier_thickening_disjoint

example : measure ℝ := volume
#check measure_space.volume
#check real.measure_space.volume

/- lemma exists_null_infdist_level
  [pseudo_emetric_space α] --[measurable_space α]
  [opens_measurable_space α]
  (μ : measure α) [sigma_finite μ] (s : set α) {R : ℝ≥0∞} (R_pos : 0 < R) :
  ∃ r ∈ Ioo 0 R, μ {x : α | emetric.inf_edist x s = r} = 0 :=
begin
  set R₁ := min 1 R with def_R₁,
  --have R₁_le_one : R₁ ≤ 1, from min_le_left 1 R,
  --have R₁_le_R : R₁ ≤ R, from min_le_right 1 R,
  have R₁_lt_top : R₁ < ∞, from lt_of_le_of_lt (min_le_left 1 R) ennreal.one_lt_top,
  have R₁_pos : 0 < R₁, from lt_min ennreal.zero_lt_one R_pos,
  suffices : ∃ r ∈ Ioo 0 R₁, μ {x : α | emetric.inf_edist x s = r} = 0,
  { rcases this with ⟨r, ⟨r_in_Ioo₁, hr⟩⟩,
    exact ⟨r, ⟨Ioo_subset_Ioo le_rfl (min_le_right 1 R) r_in_Ioo₁, hr⟩⟩, },
  --have : ¬ set.countable (Ioo 0 R),
  --{ have := uncountable
  --  sorry, },
  --change ∃ r ∈ Ioo 0 R, μ ((λ x, emetric.inf_edist x s) ⁻¹' {r}) = 0,
  have mbles : ∀ (r : ℝ), measurable_set ((λ x, emetric.inf_edist x s) ⁻¹' {ennreal.of_real r}),
    from λ r, measurable_set_preimage measurable_inf_edist (measurable_set_singleton _),
  have mbles' : ∀ (r : ℝ≥0∞), measurable_set ((λ x, emetric.inf_edist x s) ⁻¹' {r}),
    from λ r, measurable_set_preimage measurable_inf_edist (measurable_set_singleton r),
  have disjs : pairwise (disjoint on λ (r : ℝ), (λ (x : α), emetric.inf_edist x s) ⁻¹' {ennreal.of_real r}),
  { intros r₁ r₂ hr,
    change disjoint _ _,
    by_cases sign_r₁ : r₁ < 0,
    { simp only, },
    by_cases sign_r₂ : r₂ < 0,
    { simp [sign_r₂], },
    apply disjoint.preimage,
    rw disjoint_singleton,
    rw [← disjoint_iff_inter_eq_empty],
    change disjoint ((λ x, emetric.inf_edist x A) ⁻¹' {ennreal.of_real r₁})
                    ((λ x, emetric.inf_edist x A) ⁻¹' {ennreal.of_real r₂}),
    apply disjoint.preimage,
    rw disjoint_singleton,
    rw [ennreal.of_real_eq_coe_nnreal (show (0 : ℝ) ≤ r₁, by linarith),
        ennreal.of_real_eq_coe_nnreal (show (0 : ℝ) ≤ r₂, by linarith)],
    simp only [ne.def, ennreal.coe_eq_coe, subtype.mk_eq_mk],
    exact hr, },
/-   { rintros r₁ r₂ hr x ⟨hx₁, hx₂⟩,
    simp only [mem_preimage, mem_singleton_iff] at hx₁ hx₂,
    --exact hr (hx₁ ▸ hx₂),
    sorry, },
 -/
  have disjs' : pairwise (disjoint on λ (r : ℝ≥0∞), (λ (x : α), emetric.inf_edist x s) ⁻¹' {r}),
  { rintros r₁ r₂ hr x ⟨hx₁, hx₂⟩,
    exact hr (hx₁ ▸ hx₂), },
  have key := @countable_meas_pos_of_disjoint_Union α _ _ μ _ _ mbles disjs,
  dsimp at key,
  have key' : {r : ℝ | r ∈ Ioi (0 : ℝ) ∧
          (0 < μ ((λ (x : α), emetric.inf_edist x s) ⁻¹' {ennreal.of_real r}))}.countable,
  { apply countable.mono _ key,
    simp only [set_of_subset_set_of, and_imp, imp_self, implies_true_iff], },
  have vol_Ioo : volume (Ioo 0 (R₁.to_real)) = R₁,
  { simp only [real.volume_Ioo, tsub_zero, ennreal.of_real_to_real, ne.def, min_eq_top,
               ennreal.one_ne_top, false_and, not_false_iff], },
  have tada : volume ((Ioo 0 (R₁.to_real)) \ {r : ℝ | r ∈ Ioi (0 : ℝ) ∧
          (0 < μ ((λ (x : α), emetric.inf_edist x s) ⁻¹' {ennreal.of_real r}))}) = R₁,
    by rwa measure_diff_null (set.countable.measure_zero key' volume),
  have tada' := lt_of_lt_of_le R₁_pos le_rfl,
  rw [← tada] at tada',
  rcases nonempty_of_measure_ne_zero tada'.ne.symm with ⟨r, ⟨r_in_Ioo₁, hr⟩⟩,
  use ennreal.of_real r,
  refine ⟨⟨ennreal.of_real_pos.mpr r_in_Ioo₁.1, _⟩, _⟩,
  { exact (ennreal.of_real_lt_iff_lt_to_real r_in_Ioo₁.1.le R₁_lt_top.ne).mpr r_in_Ioo₁.2, },
  { simp only [mem_Ioi, mem_set_of_eq, not_and, not_lt, le_zero_iff] at hr,
    exact hr (r_in_Ioo₁.1), },
end
 -/

variables [topological_space α]

--#check tendsto_sup
--#check measure_theory.measure_eq_infi

-- Q: Do we not have monotone convergence theorems for measures (instead of integrals)?

#check set.indicator_le_indicator_of_subset

--lemma set.indicator_le_indicator_of_subset {β γ : Type*} [linear_order γ] :

#check tendsto_at_top_csupr
#check tendsto_at_top_supr

/- lemma monotone.tendsto_nhds_supr {xs : ℕ → ℝ≥0∞} (xs_mono : monotone xs) :
  tendsto xs at_top (𝓝 (⨆ n, xs n)) :=
begin
  sorry,
end
 -/

/- -- Maybe the monotonicity assumption is not great...
-- (Although in pen-and-paper math this is what one would usually find.)
lemma monotone.tendsto_measure {α : Type*} [measurable_space α]
  {As : ℕ → set α} (As_incr : monotone As) (As_mble : ∀ n, measurable_set (As n))
  (μ : measure α) :
  tendsto (λ n, μ (As n)) at_top (𝓝 (μ (⋃ i, As i))) :=
begin
  set fs : ℕ → α → ℝ≥0∞ := λ n, (As n).indicator (λ _, 1) with def_fs,
  have fs_mble : ∀ n, measurable (fs n),
    from λ n, measurable.indicator measurable_const (As_mble n),
  have fs_mono : monotone fs,
    from λ n m hnm x, indicator_le_indicator_of_subset (As_incr hnm) (λ _, zero_le_one) x,
  have supr_fs_eq : ∀ x, (⨆ n, fs n x) = (⋃ i, As i).indicator (λ _, 1) x,
    from λ x, by simp only [def_fs, indicator_Union_apply, ennreal.bot_eq_zero],
  have key := @measure_theory.lintegral_supr _ _ μ _ fs_mble fs_mono,
  simp only [def_fs, supr_fs_eq] at key,
  rw lintegral_indicator (λ _, 1) (measurable_set.Union As_mble) at key,
  simp_rw lintegral_indicator (λ _, 1) (As_mble _) at key,
  simp only [lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter] at key,
  convert tendsto_at_top_supr
    (show monotone (λ n, μ (As n)), from λ n m hnm, outer_measure.mono _ (As_incr hnm)),
end
 -/

-- The following counterpart of `mul_indicator_Union_apply` is missing?
@[to_additive] lemma _root_.set.mul_indicator_Inter_apply {α ι M}
  [nonempty ι] [complete_lattice M] [has_one M]
  (h1 : (⊥:M) = 1) (s : ι → set α) (f : α → M) (x : α) :
  mul_indicator (⋂ i, s i) f x = ⨅ i, mul_indicator (s i) f x :=
begin
  by_cases hx : x ∈ ⋂ i, s i,
  { rw [mul_indicator_of_mem hx],
    rw [mem_Inter] at hx,
    refine le_antisymm _ _,
    { apply le_infi,
      intros j,
      simp only [mul_indicator_of_mem (hx j)], },
    { simp only [mul_indicator_of_mem (hx _)],
      apply infi_le _ ‹nonempty ι›.some, }, },
  { rw [mul_indicator_of_not_mem hx],
    simp only [mem_Inter, not_exists, not_forall] at hx,
    cases hx with j hj,
    refine le_antisymm (by { rw ← h1, exact bot_le, }) _,
    simpa [mul_indicator_of_not_mem hj] using (infi_le (λ i, (s i).mul_indicator f) j) x, },
end

#check set.indicator_Inter_apply

/- lemma _root_.set.add_indicator_Inter_apply {α ι M} [nonempty ι] [complete_lattice M] [has_zero M]
  (h1 : (⊥:M) = 0) (s : ι → set α) (f : α → M) (x : α) :
  indicator (⋂ i, s i) f x = ⨅ i, indicator (s i) f x :=
begin
  by_cases hx : x ∈ ⋂ i, s i,
  { rw [indicator_of_mem hx],
    rw [mem_Inter] at hx,
    refine le_antisymm _ _,
    { apply le_infi,
      intros j,
      simp only [indicator_of_mem (hx j)], },
    { simp only [indicator_of_mem (hx _)],
      apply infi_le _ ‹nonempty ι›.some, }, },
  { rw [indicator_of_not_mem hx],
    simp only [mem_Inter, not_exists, not_forall] at hx,
    cases hx with j hj,
    refine le_antisymm (by { rw ← h1, exact bot_le, }) _,
    simpa [indicator_of_not_mem hj] using (infi_le (λ i, (s i).indicator f) j) x, },
end
 -/
/- -- Maybe the monotonicity assumption is not great...
-- (Although in pen-and-paper math this is what one would usually find.)
lemma antitone.tendsto_measure {α : Type*} [measurable_space α]
  {As : ℕ → set α} (As_decr : antitone As) (As_mble : ∀ n, measurable_set (As n))
  (μ : measure α) (meas_ne_top : μ (As 0) ≠ ⊤) :
  tendsto (λ n, μ (As n)) at_top (𝓝 (μ (⋂ i, As i))) :=
begin
  set fs : ℕ → α → ℝ≥0∞ := λ n, (As n).indicator (λ _, 1) with def_fs,
  have fs_mble : ∀ n, measurable (fs n),
    from λ n, measurable.indicator measurable_const (As_mble n),
  have fs_anti : antitone fs,
    from λ n m hnm x, indicator_le_indicator_of_subset (As_decr hnm) (λ _, zero_le_one) x,
  have infi_fs_eq : ∀ x, (⨅ n, fs n x) = (⋂ i, As i).indicator (λ _, 1) x,
    from λ x, by simp only [set.add_indicator_Inter_apply, ennreal.bot_eq_zero],
  convert tendsto_at_top_infi
    (show antitone (λ n, μ (As n)), from λ n m hnm, outer_measure.mono _ (As_decr hnm)),
  have key := @measure_theory.lintegral_infi _ _ μ _ fs_mble fs_anti,
  simp only [def_fs, infi_fs_eq] at key,
  rw lintegral_indicator (λ _, 1) (measurable_set.Inter As_mble) at key,
  simp_rw lintegral_indicator (λ _, 1) (As_mble _) at key,
  simp only [lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter, ne.def] at key,
  exact key meas_ne_top,
end

lemma antitone.tendsto_measure_of_is_finite_measure {α : Type*} [measurable_space α]
  {As : ℕ → set α} (As_decr : antitone As) (As_mble : ∀ n, measurable_set (As n))
  (μ : measure α) [is_finite_measure μ] :
  tendsto (λ n, μ (As n)) at_top (𝓝 (μ (⋂ i, As i))) :=
antitone.tendsto_measure As_decr As_mble μ (measure_ne_top μ (As 0))
 -/

/- lemma closure_eq_Inter_thickening'' {α : Type*} [pseudo_emetric_space α] (E : set α)
  (s : set ℝ) (hs₀ : s ⊆ Ioi 0) (hs : cluster_pt (0 : ℝ) (principal s)) :
  closure E = ⋂ δ ∈ s, metric.thickening δ E :=
begin
  apply metric.closure_eq_Inter_thickening' E s hs₀,
  intros ε ε_pos,
  rw cluster_pt_principal_iff at hs,
  specialize hs (metric.closed_ball 0 ε) (metric.closed_ball_mem_nhds _ ε_pos),
  rw [inter_comm, (show s = s ∩ Ioi 0, by rw inter_eq_self_of_subset_left hs₀)] at hs,
  rw [real.closed_ball_eq_Icc, zero_sub, zero_add, inter_assoc] at hs,
  rwa [show Ioi (0 : ℝ) ∩ Icc (-ε) ε = Ioc 0 ε, from _] at hs,
  ext x,
  exact ⟨(λ hx, ⟨hx.1, hx.2.2⟩), (λ hx, ⟨hx.1, ⟨by linarith [hx.1], hx.2⟩⟩)⟩,
end
 -/

/- lemma tendsto_measure_thickening_of_is_closed''
  {α : Type*} [measurable_space α] [pseudo_emetric_space α] [opens_measurable_space α]
  (μ : measure α) [is_finite_measure μ] {F : set α} (F_closed : is_closed F) {δs : ℕ → ℝ}
  (δs_pos : ∀ n, 0 < δs n) (δs_lim : tendsto δs at_top (𝓝 0)) (δs_decr : antitone δs) :
  tendsto (λ n, μ (metric.thickening (δs n) F)) at_top (𝓝 (μ F)) :=
begin
  set As := (λ n, metric.thickening (δs n) F) with def_As,
  have As_decr : antitone As, from λ n m hnm, metric.thickening_mono (δs_decr hnm) F,
  have As_mble : ∀ n, measurable_set (As n), from λ n, metric.is_open_thickening.measurable_set,
  have key := antitone.tendsto_measure As_decr As_mble μ (measure_ne_top μ (As 0)),
  have Inter_As_eq : (⋂ n, As n) = (⋂ δ ∈ range δs, metric.thickening δ F),
  { ext x, simp only [mem_range, Inter_exists, Inter_Inter_eq', imp_self], },
  rw Inter_As_eq at key,
  rw [← closure_eq_Inter_thickening'' F (range δs) _ _] at key,
  rw [F_closed.closure_eq] at key,
  exact key,
  { rw range_subset_iff,
    exact λ n, δs_pos n, },
  { rw ← mem_closure_iff_cluster_pt,
    exact mem_closure_of_tendsto δs_lim (eventually_of_forall mem_range_self), },
end
 -/

lemma lintegral_indicator_one {α : Type*} [measurable_space α] (μ : measure α)
  {s : set α} (s_mble : measurable_set s) :
  ∫⁻ x, (s.indicator (λ _, (1 : ℝ≥0∞)) x) ∂μ = μ s :=
by simp [lintegral_indicator _ s_mble]

lemma tendsto_measure_of_tendsto_indicator
  {α ι : Type*} (L : filter ι) [is_countably_generated L]
  [measurable_space α] (μ : measure α) [is_finite_measure μ] {A : set α} (A_mble : measurable_set A)
  {As : ι → set α} (As_mble : ∀ i, measurable_set (As i))
  (h_lim : ∀ᵐ x ∂μ, tendsto (λ i, (As i).indicator (λ _, (1 : ℝ≥0∞)) x) L (𝓝 (A.indicator (λ _, (1 : ℝ≥0∞)) x))) :
  tendsto (λ i, μ (As i)) L (𝓝 (μ A)) :=
begin
  simp_rw [← lintegral_indicator_one μ A_mble, ← lintegral_indicator_one μ (As_mble _)],
  refine tendsto_lintegral_filter_of_dominated_convergence (λ _, (1 : ℝ≥0∞))
          (eventually_of_forall _) (eventually_of_forall _)  _ h_lim,
  { exact λ n, measurable.indicator measurable_const (As_mble n), },
  { intros n,
    apply eventually_of_forall,
    exact λ x, indicator_apply_le (λ _, le_refl _), },
  { rw [lintegral_one],
    exact (measure_lt_top μ univ).ne, },
end

/- lemma tendsto_measure_of_tendsto_indicator₀
  {α : Type*} [measurable_space α] (μ : measure α) [is_finite_measure μ] {A : set α} (A_mble : measurable_set A)
  {As : ℕ → set α} (As_mble : ∀ i, measurable_set (As i))
  (h_lim : ∀ᵐ x ∂μ, tendsto (λ i, (As i).indicator (λ _, (1 : ℝ≥0∞)) x) at_top (𝓝 (A.indicator (λ _, (1 : ℝ≥0∞)) x))) :
  tendsto (λ i, μ (As i)) at_top (𝓝 (μ A)) :=
begin
  simp_rw [← lintegral_indicator_one μ A_mble, ← lintegral_indicator_one μ (As_mble _)],
  refine tendsto_lintegral_filter_of_dominated_convergence (λ _, (1 : ℝ≥0∞)) (eventually_of_forall _) (eventually_of_forall _)  _ h_lim,
  { exact λ n, measurable.indicator measurable_const (As_mble n), },
  { intros n,
    apply eventually_of_forall,
    exact λ x, indicator_apply_le (λ _, le_refl _), },
  { rw [lintegral_one],
    exact (measure_lt_top μ univ).ne, },
end
 -/

/- lemma tendsto_indicator_thickening_indicator_closure {α : Type*} [pseudo_emetric_space α]
  (f : α → ℝ≥0∞) {δs : ℕ → ℝ} (δs_pos : ∀ n, 0 < δs n) (δs_lim : tendsto δs at_top (𝓝 0)) (E : set α) :
  tendsto (λ n, (metric.thickening (δs n) E).indicator f) at_top (𝓝 (indicator (closure E) f)) :=
begin
  rw tendsto_pi_nhds,
  intro x,
  by_cases x_mem_closure : x ∈ closure E,
  { simp only [x_mem_closure, (λ n, closure_subset_thickening (δs_pos n) E x_mem_closure), indicator_of_mem],
    exact tendsto_const_nhds, },
  { have pos_dist : 0 < inf_edist x (closure E),
    { rw mem_iff_inf_edist_zero_of_closed is_closed_closure at x_mem_closure,
      exact zero_lt_iff.mpr x_mem_closure, },
    obtain ⟨ε, ⟨ε_pos, ε_le⟩⟩ : ∃ (ε : ℝ), 0 < ε ∧ ennreal.of_real ε ≤ inf_edist x E,
    { by_cases dist_infty : inf_edist x E = ∞,
      { rw dist_infty,
        use [1, zero_lt_one, le_top], },
      { use (inf_edist x E).to_real,
        refine ⟨(ennreal.to_real_lt_to_real ennreal.zero_ne_top dist_infty).mpr _,
                ennreal.of_real_to_real_le⟩,
        rwa inf_edist_closure at pos_dist, }, },
    rw metric.tendsto_nhds at δs_lim,
    specialize δs_lim ε ε_pos,
    simp only [dist_zero_right, real.norm_eq_abs, eventually_at_top, ge_iff_le] at δs_lim,
    rcases δs_lim with ⟨N, hN⟩,
    apply @tendsto_at_top_of_eventually_const _ _ _ _ _ _ _ N,
    intros n n_large,
    have key : x ∉ thickening ε E, by rwa [thickening, mem_set_of_eq, not_lt],
    have key' : x ∉ thickening (δs n) E,
    { intros con,
      have δ_small : δs n ≤ ε, from (abs_lt.mp (hN n n_large)).2.le,
      have oops := thickening_mono δ_small E con,
      contradiction, },
    simp only [x_mem_closure, key', indicator_of_not_mem, not_false_iff], },
end
 -/

-- PR #17648
@[to_additive]
lemma tendsto_mul_indicator_thickening_mul_indicator_closure
  {α : Type*} [pseudo_emetric_space α] {β : Type*} [has_one β] [topological_space β] (f : α → β) (E : set α) :
  tendsto (λ δ, (metric.thickening δ E).mul_indicator f) (𝓝[>] 0)
    (𝓝 (mul_indicator (closure E) f)) :=
sorry

lemma tendsto_measure_thickening_nhds_measure_closure
  {α : Type*} [measurable_space α] [pseudo_emetric_space α] [opens_measurable_space α]
  (μ : measure α) [is_finite_measure μ] {E : set α} :
  tendsto (λ δ, μ (metric.thickening δ E)) (𝓝[>] (0 : ℝ)) (𝓝 (μ (closure E))) :=
begin
  refine tendsto_measure_of_tendsto_indicator (𝓝[>] (0 : ℝ)) μ is_closed_closure.measurable_set
          (λ δ, (@metric.is_open_thickening _ _ δ E).measurable_set) _,
  apply eventually_of_forall,
  intros x,
  have key := tendsto_indicator_thickening_indicator_closure (λ _, (1 : ℝ≥0∞)) E,
  rw tendsto_pi_nhds at key,
  exact key x,
end

/- lemma tendsto_measure_thickening_nhds_measure_closure₀
  {α : Type*} [measurable_space α] [pseudo_emetric_space α] [opens_measurable_space α]
  (μ : measure α) [is_finite_measure μ] {E : set α} {δs : ℕ → ℝ}
  (δs_pos : ∀ n, 0 < δs n) (δs_lim : tendsto δs at_top (𝓝 0)) :
  tendsto (λ n, μ (metric.thickening (δs n) E)) at_top (𝓝 (μ (closure E))) :=
begin
  refine tendsto_measure_of_tendsto_indicator μ is_closed_closure.measurable_set
          (λ n, (@metric.is_open_thickening _ _ (δs _) E).measurable_set) _,
  apply eventually_of_forall,
  intros x,
  --have key := tendsto_indicator_thickening_indicator_closure (λ _, 1) δs_pos δs_lim E,
  --rw tendsto_pi_nhds at key,
  --exact key x,
  sorry,
end
 -/

lemma tendsto_measure_thickening_of_is_closed
  {α : Type*} [measurable_space α] [pseudo_emetric_space α] [opens_measurable_space α]
  (μ : measure α) [is_finite_measure μ] {F : set α} (F_closed : is_closed F) :
  tendsto (λ δ, μ (metric.thickening δ F)) (𝓝[>] (0 : ℝ)) (𝓝 (μ F)) :=
begin
  convert tendsto_measure_thickening_nhds_measure_closure μ,
  exact F_closed.closure_eq.symm,
end

/- lemma tendsto_measure_thickening_of_is_closed₀
  {α : Type*} [measurable_space α] [pseudo_emetric_space α] [opens_measurable_space α]
  (μ : measure α) [is_finite_measure μ] {F : set α} (F_closed : is_closed F) {δs : ℕ → ℝ}
  (δs_pos : ∀ n, 0 < δs n) (δs_lim : tendsto δs at_top (𝓝 0)) :
  tendsto (λ n, μ (metric.thickening (δs n) F)) at_top (𝓝 (μ F)) :=
begin
  convert tendsto_measure_thickening_nhds_measure_closure μ δs_pos δs_lim,
  exact F_closed.closure_eq.symm,
end
 -/

/- lemma tendsto_measure_thickening_of_is_closed'
  {α : Type*} [measurable_space α] [pseudo_emetric_space α] [opens_measurable_space α]
  (μ : measure α) [is_finite_measure μ] {F : set α} (F_closed : is_closed F) {δs : ℕ → ℝ}
  (δs_pos : ∀ n, 0 < δs n) (δs_lim : tendsto δs at_top (𝓝 0)) :
  tendsto (λ n, μ (metric.thickening (δs n) F)) at_top (𝓝 (μ F)) :=
begin
  set fs := (λ n, (metric.thickening (δs n) F).indicator (λ _, (1 : ℝ≥0∞))) with def_fs,
  have fs_mble : ∀ n, measurable (fs n),
  { sorry, },
  --have fs_bdd :
  --have Ω α
  convert tendsto_lintegral_filter_of_dominated_convergence 1
          (eventually_of_forall fs_mble)
          _
          (@lintegral_const_lt_top _ _ μ _ _ (@ennreal.coe_ne_top 1)).ne _,
  { funext n,
    rw [def_fs, lintegral_indicator (λ _, 1) (@is_open_thickening _ _ (δs n) F).measurable_set],
    simp only [lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter], },
  {
    sorry, },
  { exact at_top.is_countably_generated, },
  { sorry, },
  { apply eventually_of_forall,
    intros n,
    apply eventually_of_forall,
    exact indicator_le_self (thickening (δs n) F) (λ _, (1 : ℝ≥0∞)), },
  { sorry, },
  --convert this,
  funext n,
  rw [def_fs, lintegral_indicator _ (@is_open_thickening _ _ (δs n) F).measurable_set],
  simp only [lintegral_one, measure.restrict_apply, measurable_set.univ, univ_inter],
  rw [lintegral_indicator (F.indicator (λ _, 1)) F_closed.measurable_set],
  { rw [lintegral_indicator _ F_closed.measurable_set],
    simp only [lintegral_one, measure.restrict_apply, measurable_set.univ,
               univ_inter, measure.restrict_apply_self], },
  { exact at_top.is_countably_generated, },
  { apply eventually_of_forall,
    intros n,
    apply eventually_of_forall,
    exact indicator_le_self (thickening (δs n) F) (λ _, (1 : ℝ≥0∞)), },
end
 -/

lemma borel_condition_implies_closed_condition
  {α ι : Type*} {L : filter ι} [ne_bot L]
  [measurable_space α] [pseudo_emetric_space α] [opens_measurable_space α]
  {μ : probability_measure α} {μs : ι → probability_measure α}
  (h : ∀ {E : set α}, measurable_set E → μ (frontier E) = 0 → tendsto (λ i, μs i E) L (𝓝 (μ E)))
  (F : set α) (F_closed : is_closed F) :
  L.limsup (λ i, (μs i : measure α) F) ≤ (μ : measure α) F :=
begin
  have ex := exists_null_frontiers_thickening' α μ F,
  let rs := classical.some ex,
  have rs_lim : tendsto rs at_top (𝓝[>] 0), from (classical.some_spec ex).1,
  have rs_pos : ∀ n, 0 < rs n, by sorry, --from λ n, ((classical.some_spec ex).2 n).1,
  have rs_null : ∀ n, (μ : measure α) (frontier (metric.thickening (rs n) F)) = 0,
    from λ n, ((classical.some_spec ex).2 n),
  have Fthicks_open : ∀ n, is_open (metric.thickening (rs n) F),
    from λ n, metric.is_open_thickening,
  have key := λ (n : ℕ), h (Fthicks_open n).measurable_set
                  (by { specialize rs_null n, rwa probability_measure.coe_null_iff at rs_null, }),
  -- limsupᵢ (μᵢ F) ≤ limsupᵢ (μᵢ Fδ) = limᵢ (μᵢ Fδ) = μ Fδ ≤ μ F + ε
  apply ennreal.le_of_forall_pos_le_add,
  intros ε ε_pos μF_finite,
/-   have aux' := λ n, λ i, @measure_mono _ _ (μs i : measure α) _ _ (metric.self_subset_thickening (rs_pos n) F),
  have aux : ∀ n,
      (λ i, (μs i : measure α) F) ≤ᶠ[L] (λ i, (μs i : measure α) (metric.thickening (rs n) F)),
    from λ n, eventually_of_forall (aux' n),
  have := λ n, limsup_le_limsup (aux n),
 -/
  --have := @measure_mono _ _ (μ : measure α),

  have keyB := tendsto_measure_thickening_of_is_closed (μ : measure α) F_closed,
  have nhd : Iio ((μ : measure α) F  + ε) ∈ 𝓝 ((μ : measure α) F),
  { apply Iio_mem_nhds,
    simpa only [add_zero] using ennreal.add_lt_add_left μF_finite.ne (ennreal.coe_pos.mpr ε_pos), },
  specialize rs_lim (keyB nhd),
  simp only [mem_map, mem_at_top_sets, ge_iff_le, mem_preimage, mem_Iio] at rs_lim,
  rcases rs_lim with ⟨m, hm⟩,
  have whee := hm m rfl.le,
  have aux' := λ i, @measure_mono _ _ (μs i : measure α) _ _ (metric.self_subset_thickening (rs_pos m) F),
  --refine (limsup_le_limsup (eventually_of_forall aux')).trans _,
  have aux : (λ i, (μs i : measure α) F)
              ≤ᶠ[L] (λ i, (μs i : measure α) (metric.thickening (rs m) F)),
    from eventually_of_forall aux',
  refine (limsup_le_limsup aux).trans _,
  --have := tendsto.limsup_eq,
  have := key m, -- Should do `⇑↑(μs i)` instead of `↑(μs i)`. :(
  have := tendsto.limsup_eq (key m),

  --rw this,

  -- specialize keyB nhd,
  -- simp only [mem_map] at keyB,


  --rcases mem_nhds_within_Ioi_iff_exists_Ioo_subset.mp keyB with ⟨δ₀, ⟨δ₀_pos, hδ₀⟩⟩,
  --rcases nonempty_Ioo.mpr δ₀_pos with ⟨δ', hδ'⟩,

  --have := tendsto_mono,
  --have := finite_measure.tendsto
  --have := le_of_forall_pos
  sorry,
end

lemma borel_condition_implies_closed_condition'
  {α ι : Type*} {L : filter ι}
  [measurable_space α] [pseudo_emetric_space α] [opens_measurable_space α]
  {μ : probability_measure α} {μs : ι → probability_measure α}
  (h : ∀ {E : set α}, measurable_set E → μ (frontier E) = 0 → tendsto (λ i, μs i E) L (𝓝 (μ E)))
  (F : set α) (F_closed : is_closed F) :
  L.limsup (λ i, (μs i : measure α) F) ≤ (μ : measure α) F :=
begin
  have ex := exists_null_frontiers_thickening α μ F,
  let rs := classical.some ex,
  have rs_lim : tendsto rs at_top (𝓝 0), from (classical.some_spec ex).1,
  have rs_pos : ∀ n, 0 < rs n, from λ n, ((classical.some_spec ex).2 n).1,
  have rs_null : ∀ n, (μ : measure α) (frontier (metric.thickening (rs n) F)) = 0,
    from λ n, ((classical.some_spec ex).2 n).2,
  --have := λ n, rs_null n,
  have Fthicks_open : ∀ n, is_open (metric.thickening (rs n) F),
    from λ n, metric.is_open_thickening,
  --have := λ n, (Fthicks_open n).measurable_set,
  have keyA := λ (n : ℕ), h (Fthicks_open n).measurable_set
                  (by { specialize rs_null n, rwa probability_measure.coe_null_iff at rs_null, }),
  -- limsupᵢ (μᵢ F) ≤ limsupᵢ (μᵢ Fδ) = limᵢ (μᵢ Fδ) = μ Fδ ≤ μ F + ε
  --have auxB := tendsto_indicator_thickening_indicator_closure,
  apply ennreal.le_of_forall_pos_le_add,
  intros ε ε_pos μF_finite,
  --have := limsup_le_limsup,
  --have := limsup_le_limsup,
  --have : ∀ᶠ i in at_top, ((μs (rs i) : measure α) F) ≤ (μ : measure α) F + ε, by sorry,
  have keyB := tendsto_measure_thickening_of_is_closed (μ : measure α) F_closed,
  --have μF_finite : (μ : measure α) F < ∞, from measure_lt_top _ _,
  have nhd : Iio ((μ : measure α) F  + ε) ∈ 𝓝 ((μ : measure α) F),
  { apply Iio_mem_nhds,
    simpa only [add_zero] using ennreal.add_lt_add_left μF_finite.ne (ennreal.coe_pos.mpr ε_pos), },
  --have key := keyA,
  --have := tendsto_nhds_withi
  specialize keyB nhd,
  simp only [mem_map] at keyB,
  rcases mem_nhds_within_Ioi_iff_exists_Ioo_subset.mp keyB with ⟨δ₀, ⟨δ₀_pos, hδ₀⟩⟩,
  rcases nonempty_Ioo.mpr δ₀_pos with ⟨δ', hδ'⟩,
  --have : ∃ δ' ∈ Ioo 0 δ₀, from this,
  --have := tendsto_mono,
  --have := finite_measure.tendsto
  --have := le_of_forall_pos
  sorry,
end

end borel_imp -- section
-/
