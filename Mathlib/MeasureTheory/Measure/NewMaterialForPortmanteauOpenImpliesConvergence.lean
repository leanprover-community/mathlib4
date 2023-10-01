import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic

/-!
# Outline of portmanteau implication: liminf condition for open sets implies weak convergence

This file contains steps needed to prove the portmanteau implication
`le_liminf_open_implies_convergence`. Some intermediate steps need to be generalized
and cleaned up, and are to be placed in appropriate files. The main part should go
to the file `Mathlib.MeasureTheory.Measure.Portmanteau`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal BoundedContinuousFunction Topology

-- NOTE: Missing from Mathlib?
-- What would be a good generality?
-- (Mixes order-boundedness and metric-boundedness, so typeclasses don't readily exist.)
lemma Filter.isBounded_le_map_of_bounded_range {ι : Type*} (F : Filter ι) {f : ι → ℝ}
    (h : Bornology.IsBounded (Set.range f)) :
    (F.map f).IsBounded (· ≤ ·) := by
  rw [Real.isBounded_iff_bddBelow_bddAbove] at h
  obtain ⟨c, hc⟩ := h.2
  refine isBoundedUnder_of ⟨c, by simpa [mem_upperBounds] using hc⟩

lemma Filter.isBounded_ge_map_of_bounded_range {ι : Type*} (F : Filter ι) {f : ι → ℝ}
    (h : Bornology.IsBounded (Set.range f)) :
    (F.map f).IsBounded (· ≥ ·) := by
  rw [Real.isBounded_iff_bddBelow_bddAbove] at h
  obtain ⟨c, hc⟩ := h.1
  apply isBoundedUnder_of ⟨c, by simpa [mem_lowerBounds] using hc⟩



section le_liminf_open_implies_convergence

variable {Ω : Type} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

-- NOTE: I think I will work with real-valued integrals, after all...
lemma fatou_argument_lintegral
    {μ : Measure Ω} [SigmaFinite μ] {μs : ℕ → Measure Ω} [∀ i, SigmaFinite (μs i)]
    {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂ (μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (eventually_of_forall f_nn) f_cont.aemeasurable]
  calc  ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a}
      ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, atTop.liminf (fun i ↦ (μs i) {a | t < f a})
            := (lintegral_mono (fun t ↦ h_opens _ (continuous_def.mp f_cont _ isOpen_Ioi))).trans ?_
    _ ≤ atTop.liminf (fun i ↦ ∫⁻ (t : ℝ) in Set.Ioi 0, (μs i) {a | t < f a})
            := lintegral_liminf_le (fun n ↦ Antitone.measurable
                (fun s t hst ↦ measure_mono (fun ω hω ↦ lt_of_le_of_lt hst hω)))
  rfl

-- NOTE: I think this is the version I prefer to use, after all...
lemma fatou_argument_integral_nonneg
    {μ : Measure Ω} [IsFiniteMeasure μ] {μs : ℕ → Measure Ω} [∀ i, IsFiniteMeasure (μs i)]
    {f : Ω →ᵇ ℝ} (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
      ∫ x, (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)) := by
  have earlier := fatou_argument_lintegral f.continuous f_nn h_opens
  rw [@integral_eq_lintegral_of_nonneg_ae Ω _ μ f (eventually_of_forall f_nn)
        f.continuous.measurable.aestronglyMeasurable]
  convert (ENNReal.toReal_le_toReal ?_ ?_).mpr earlier
  · simp only [fun i ↦ @integral_eq_lintegral_of_nonneg_ae Ω _ (μs i) f (eventually_of_forall f_nn)
                        f.continuous.measurable.aestronglyMeasurable]
    --have := @Monotone.map_liminf_of_continuousAt
    sorry
  · sorry
  · sorry

-- A direct proof attempt (should be discarded).
lemma fatou_argument_integral_nonneg'
    {μ : Measure Ω} [IsFiniteMeasure μ] {μs : ℕ → Measure Ω} [∀ i, IsFiniteMeasure (μs i)]
    {f : Ω →ᵇ ℝ} (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
      ∫ x, (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)) := by
  simp_rw [(f.integrable _).integral_eq_integral_meas_lt (eventually_of_forall f_nn)]
  have rwr := @integral_eq_lintegral_of_nonneg_ae ℝ _ (volume.restrict (Set.Ioi 0))
          (fun t ↦ ENNReal.toReal (μ {x | t < f x})) (eventually_of_forall ?_) ?_
  have rwr' := fun i ↦ @integral_eq_lintegral_of_nonneg_ae ℝ _ (volume.restrict (Set.Ioi 0))
            (fun t ↦ ENNReal.toReal (μs i {x | t < f x})) (eventually_of_forall ?_) ?_
  simp only [rwr, ne_eq, rwr', ge_iff_le]
  · --have aux : ∀ t, IsOpen {a : Ω | t < f a} :=
    --  fun t ↦ (continuous_def.mp f.continuous) _ isOpen_Ioi
    --have obs := fun t ↦ h_opens _ (aux t)
    --have := @lintegral_liminf_le

    --have earlier := fatou_argument_lintegral f.continuous f_nn h_opens
    sorry
  · exact fun _ ↦ by simp only [Pi.zero_apply, ENNReal.toReal_nonneg]
  · apply Measurable.aestronglyMeasurable
    apply ENNReal.measurable_toReal.comp (Antitone.measurable ?_)
    exact fun x y hxy ↦ measure_mono (fun z hz ↦ lt_of_le_of_lt hxy hz)
  · exact fun _ ↦ by simp only [Pi.zero_apply, ENNReal.toReal_nonneg]
  · apply Measurable.aestronglyMeasurable
    apply ENNReal.measurable_toReal.comp (Antitone.measurable ?_)
    exact fun x y hxy ↦ measure_mono (fun z hz ↦ lt_of_le_of_lt hxy hz)

lemma reduction_to_liminf {ι : Type*} {L : Filter ι} [NeBot L]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ f : Ω →ᵇ ℝ, 0 ≤ f → ∫ x, (f x) ∂μ ≤ L.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)))
    (f : Ω →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, (f x) ∂ (μs i)) L (𝓝 (∫ x, (f x) ∂μ)) := by
  have obs := BoundedContinuousFunction.isBounded_range_integral μs f
  have bdd_above : IsBoundedUnder (· ≤ ·) L (fun i ↦ ∫ (x : Ω), f x ∂μs i) :=
    isBounded_le_map_of_bounded_range _ obs
  have bdd_below : IsBoundedUnder (· ≥ ·) L (fun i ↦ ∫ (x : Ω), f x ∂μs i) :=
    isBounded_ge_map_of_bounded_range _ obs
  apply @tendsto_of_le_liminf_of_limsup_le ℝ ι _ _ _ L (fun i ↦ ∫ x, (f x) ∂ (μs i)) (∫ x, (f x) ∂μ)
  · have key := h _ (f.add_norm_nonneg)
    simp_rw [f.integral_add_const ‖f‖] at key
    simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
    -- TODO: Should the case of ⊥ filter be treated separately and not included as an assumption?
    have := liminf_add_const L (fun i ↦ ∫ x, (f x) ∂ (μs i)) ‖f‖ bdd_above bdd_below
    rwa [this, add_le_add_iff_right] at key
  · have key := h _ (f.norm_sub_nonneg)
    simp_rw [f.integral_const_sub ‖f‖] at key
    simp only [measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
    have := liminf_const_sub L (fun i ↦ ∫ x, (f x) ∂ (μs i)) ‖f‖ bdd_above bdd_below
    rwa [this, sub_le_sub_iff_left] at key
  · exact bdd_above
  · exact bdd_below

-- Not needed?
/-- A characterization of weak convergence of probability measures by the condition that the
integrals of every continuous bounded nonnegative function converge to the integral of the function
against the limit measure. -/
lemma ProbabilityMeasure.tendsto_iff_forall_nonneg_integral_tendsto {γ : Type _} {F : Filter γ}
    {μs : γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω} :
    Tendsto μs F (𝓝 μ) ↔
      ∀ f : Ω →ᵇ ℝ, 0 ≤ f →
        Tendsto (fun i ↦ ∫ ω, (f ω) ∂(μs i : Measure Ω)) F (𝓝 (∫ ω, (f ω) ∂(μ : Measure Ω))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine ⟨fun h f _ ↦ h f, fun h f ↦ ?_⟩
  set g := f + BoundedContinuousFunction.const _ ‖f‖ with g_def
  have fx_eq : ∀ x, f x = g x - ‖f‖ := by
    intro x
    simp only [BoundedContinuousFunction.coe_add, BoundedContinuousFunction.const_toFun, Pi.add_apply,
               add_sub_cancel]
  have key := h g (f.add_norm_nonneg)
  simp [g_def] at key
  simp_rw [integral_add (f.integrable _) (integrable_const ‖f‖)] at key
  simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
  simp_rw [fx_eq]
  convert tendsto_add.comp (Tendsto.prod_mk_nhds key (@tendsto_const_nhds _ _ _ (-‖f‖) F)) <;> simp

theorem le_liminf_open_implies_convergence
  {ι : Type*} {μ : ProbabilityMeasure Ω} {μs : ℕ → ProbabilityMeasure Ω}
  (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    atTop.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  refine ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr ?_
  apply reduction_to_liminf
  intro f f_nn
  apply fatou_argument_integral_nonneg (f := f) f_nn
  intro G G_open
  specialize h_opens G G_open
  simp only at h_opens
  simp only [liminf, limsInf, eventually_map, eventually_atTop, ge_iff_le, le_sSup_iff] at *
  intro b b_ub
  by_cases b_eq_top : b = ∞
  · simp only [b_eq_top, le_top]
  · have foo := (@le_csSup_iff ℝ≥0 _ {a | ∃ a_1, ∀ (b : ℕ), a_1 ≤ b → a ≤ ENNReal.toNNReal (μs b G)}
              (ENNReal.toNNReal (μ G)) ?_ ?_).mp h_opens (ENNReal.toNNReal b) ?_
    · simp only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at foo
      convert ENNReal.coe_le_coe.mpr foo
      · simp only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      · simp only [ne_eq, b_eq_top, not_false_eq_true, ENNReal.coe_toNNReal]
    · use 1
      simp [mem_upperBounds]
      intro x n hn
      exact (hn n (le_refl n)).trans (ProbabilityMeasure.apply_le_one _ _)
    · refine ⟨0, by simp⟩
    · simp only [mem_upperBounds, Set.mem_setOf_eq, forall_exists_index, ne_eq,
                 ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at b_ub ⊢
      intro x n hn
      specialize b_ub x n ?_
      · intro m hm
        convert ENNReal.coe_le_coe.mpr (hn m hm)
        simp only [ne_eq, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
      · rw [(ENNReal.coe_toNNReal b_eq_top).symm] at b_ub
        exact ENNReal.coe_le_coe.mp b_ub

end le_liminf_open_implies_convergence
