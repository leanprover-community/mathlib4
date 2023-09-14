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


#check BddBelow

-- NOTE: Missing from Mathlib?
-- What would be a good generality?
-- (Mixes order-boundedness and metric-boundedness, so typeclasses don't readily exist.)
lemma Filter.isBounded_le_map_of_bounded_range {ι : Type*} (F : Filter ι) {f : ι → ℝ}
    (h : Metric.Bounded (Set.range f)) :
    (F.map f).IsBounded (· ≤ ·) := by
  rw [Real.bounded_iff_bddBelow_bddAbove] at h
  obtain ⟨c, hc⟩ := h.2
  refine isBoundedUnder_of ⟨c, by simpa [mem_upperBounds] using hc⟩

lemma Filter.isBounded_ge_map_of_bounded_range {ι : Type*} (F : Filter ι) {f : ι → ℝ}
    (h : Metric.Bounded (Set.range f)) :
    (F.map f).IsBounded (· ≥ ·) := by
  rw [Real.bounded_iff_bddBelow_bddAbove] at h
  obtain ⟨c, hc⟩ := h.1
  apply isBoundedUnder_of ⟨c, by simpa [mem_lowerBounds] using hc⟩



section layercake_for_integral

variable {α : Type*}

lemma Integrable.measure_pos_le_norm_lt_top [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {f : α → E} (f_intble : Integrable f μ) {t : ℝ} (t_pos : 0 < t) :
    μ {a : α | t ≤ ‖f a‖} < ∞ := by
  have norm_f_aemble : AEMeasurable (fun a ↦ ENNReal.ofReal ‖f a‖) μ :=
    (ENNReal.measurable_ofReal.comp measurable_norm).comp_aemeasurable f_intble.1.aemeasurable
  have markov := mul_meas_ge_le_lintegral₀ (μ := μ) norm_f_aemble (ENNReal.ofReal t)
  have obs : ∫⁻ (a : α), ENNReal.ofReal ‖f a‖ ∂μ = ∫⁻ (a : α), ‖f a‖₊ ∂μ := by
    apply lintegral_congr
    exact fun x ↦ ofReal_norm_eq_coe_nnnorm (f x)
  simp_rw [ENNReal.ofReal_le_ofReal_iff (norm_nonneg _), obs] at markov
  have almost := lt_of_le_of_lt markov f_intble.2
  have t_inv_ne_top : (ENNReal.ofReal t)⁻¹ ≠ ∞ := by
    exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr t_pos).ne.symm
  simpa [← mul_assoc,
         ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr t_pos).ne.symm ENNReal.ofReal_ne_top]
    using ENNReal.mul_lt_top t_inv_ne_top almost.ne

lemma Integrable.measure_pos_lt_norm_lt_top [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {f : α → E} (f_intble : Integrable f μ) {t : ℝ} (t_pos : 0 < t) :
    μ {a : α | t < ‖f a‖} < ∞ :=
  lt_of_le_of_lt (measure_mono (fun _ h ↦ (Set.mem_setOf_eq ▸ h).le))
    (Integrable.measure_pos_le_norm_lt_top f_intble t_pos)

lemma Integrable.measure_pos_le_lt_top [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {f : α → ℝ} (f_intble : Integrable f μ) {t : ℝ} (t_pos : 0 < t) :
    μ {a : α | t ≤ f a} < ∞ := by
  refine lt_of_le_of_lt (measure_mono ?_) (Integrable.measure_pos_le_norm_lt_top f_intble t_pos)
  intro x hx
  simp only [Real.norm_eq_abs, Set.mem_setOf_eq] at hx ⊢
  exact hx.trans (le_abs_self _)

lemma Integrable.measure_pos_lt_lt_top [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
    {f : α → ℝ} (f_intble : Integrable f μ) {t : ℝ} (t_pos : 0 < t) :
    μ {a : α | t < f a} < ∞ := by
  apply lt_of_le_of_lt (measure_mono ?_) (Integrable.measure_pos_le_lt_top f_intble t_pos)
  exact fun x hx ↦ (Set.mem_setOf_eq ▸ hx).le

-- NOTE: This is a version of the basic "Layercake formula" for real-valued nonnegative integrands
-- and Bochner integral ∫ instead of ∫⁻. I don't know if the other (more general) versions of
-- layercake should be similarly generalized. The proofs are basically similar, but the statements
-- themselves become a bit unpleasant due to integrability requirements for something slightly
-- complicated.
theorem integral_eq_integral_meas_lt [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {f : α → ℝ} (f_nn : 0 ≤ᵐ[μ] f) (f_intble : Integrable f μ) :
    (∫ ω, f ω ∂μ) = ∫ t in Set.Ioi 0, ENNReal.toReal (μ {a : α | t < f a}) := by
  have key := lintegral_eq_lintegral_meas_lt μ f_nn f_intble.aemeasurable
  have lhs_finite : ∫⁻ (ω : α), ENNReal.ofReal (f ω) ∂μ < ∞ := Integrable.lintegral_lt_top f_intble
  have rhs_finite : ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a} < ∞ := by simp only [← key, lhs_finite]
  have rhs_integrand_decr : Antitone (fun t ↦ (μ {a : α | t < f a})) :=
    fun _ _ hst ↦ measure_mono (fun _ h ↦ lt_of_le_of_lt hst h)
  have rhs_integrand_finite : ∀ (t : ℝ), t > 0 → μ {a | t < f a} < ∞ := by
    exact fun t ht ↦ Integrable.measure_pos_lt_lt_top f_intble ht
  convert (ENNReal.toReal_eq_toReal lhs_finite.ne rhs_finite.ne).mpr key
  · exact integral_eq_lintegral_of_nonneg_ae f_nn f_intble.aestronglyMeasurable
  · have aux := @integral_eq_lintegral_of_nonneg_ae _ _ ((volume : Measure ℝ).restrict (Set.Ioi 0))
      (fun t ↦ ENNReal.toReal (μ {a : α | t < f a})) ?_ ?_
    · rw [aux]
      apply congrArg ENNReal.toReal
      apply set_lintegral_congr_fun measurableSet_Ioi
      apply eventually_of_forall
      exact fun t t_pos ↦ ENNReal.ofReal_toReal (rhs_integrand_finite t t_pos).ne
    · exact eventually_of_forall (fun x ↦ by simp only [Pi.zero_apply, ENNReal.toReal_nonneg])
    · apply Measurable.aestronglyMeasurable
      refine Measurable.ennreal_toReal ?_
      apply Antitone.measurable
      exact rhs_integrand_decr

/-
theorem integral_eq_integral_meas_lt' [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    {f : α → ℝ} (f_nn : 0 ≤ f) (f_mble : Measurable f) (f_intble : Integrable f μ) :
    (∫ ω, f ω ∂μ) = ∫ t in Set.Ioi 0, ENNReal.toReal (μ {a : α | t < f a}) := by
  have key := lintegral_eq_lintegral_meas_lt μ f_nn f_mble -- should use `Integrable`
  have lhs_finite : ∫⁻ (ω : α), ENNReal.ofReal (f ω) ∂μ < ∞ := Integrable.lintegral_lt_top f_intble
  have rhs_finite : ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < f a} < ∞ := by simp only [← key, lhs_finite]
  have rhs_integrand_decr : Antitone (fun t ↦ (μ {a : α | t < f a})) :=
    fun _ _ hst ↦ measure_mono (fun _ h ↦ lt_of_le_of_lt hst h)
  have rhs_integrand_finite : ∀ (t : ℝ), t > 0 → μ {a | t < f a} < ∞ := by
    exact fun t ht ↦ Integrable.measure_pos_lt_lt_top f_intble ht
  convert (ENNReal.toReal_eq_toReal lhs_finite.ne rhs_finite.ne).mpr key
  · refine integral_eq_lintegral_of_nonneg_ae ?_ ?_
    · -- TODO: Maybe should relax the assumption to ae nonnegativity.
      exact eventually_of_forall f_nn
    · --exact f_mble.aestronglyMeasurable
      exact f_intble.aestronglyMeasurable
  · have aux := @integral_eq_lintegral_of_nonneg_ae _ _ ((volume : Measure ℝ).restrict (Set.Ioi 0))
      (fun t ↦ ENNReal.toReal (μ {a : α | t < f a})) ?_ ?_
    · rw [aux]
      apply congrArg ENNReal.toReal
      apply set_lintegral_congr_fun measurableSet_Ioi
      apply eventually_of_forall
      exact fun t t_pos ↦ ENNReal.ofReal_toReal (rhs_integrand_finite t t_pos).ne
    · exact eventually_of_forall (fun x ↦ by simp only [Pi.zero_apply, ENNReal.toReal_nonneg])
    · apply Measurable.aestronglyMeasurable
      refine Measurable.ennreal_toReal ?_
      apply Antitone.measurable
      exact rhs_integrand_decr
 -/

end layercake_for_integral



section le_liminf_open_implies_convergence

variable {Ω : Type} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
/-
-- TODO: Is it possible to add a @[gcongr] attribute to `lintegral_mono`?

attribute [gcongr] lintegral_mono -- @[gcongr] attribute only applies to lemmas proving x₁ ~₁ x₁' → ... xₙ ~ₙ xₙ' → f x₁ ... xₙ ∼ f x₁' ... xₙ', got ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} ⦃f g : α → ℝ≥0∞⦄, f ≤ g → ∫⁻ (a : α), f a ∂μ ≤ ∫⁻ (a : α), g a ∂μ

lemma foo (μ : Measure Ω) {f g : Ω → ℝ≥0∞} (hfg : f ≤ g) :
    ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, g ω ∂μ := by
  gcongr -- gcongr did not make progress
  sorry

-- This would solve it!

lemma MeasureTheory.lintegral_mono'' {α : Type} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f g : α → ℝ≥0∞}
  (hfg : f ≤ g) : lintegral μ f ≤ lintegral μ g := by sorry

#check lintegral_mono''

attribute [gcongr] lintegral_mono'' -- @[gcongr] attribute only applies to lemmas proving x₁ ~₁ x₁' → ... xₙ ~ₙ xₙ' → f x₁ ... xₙ ∼ f x₁' ... xₙ', got ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} ⦃f g : α → ℝ≥0∞⦄, f ≤ g → ∫⁻ (a : α), f a ∂μ ≤ ∫⁻ (a : α), g a ∂μ
 -/

--#check lintegral_liminf_le

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
  sorry

lemma main_thing'
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μs : ℕ → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
      ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫⁻ x, ENNReal.ofReal (f x) ∂ (μs i)) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (eventually_of_forall f_nn) f_cont.aemeasurable]
  have obs : ∀ t, IsOpen {a : Ω | t < f a} := fun t ↦ (continuous_def.mp f_cont) _ isOpen_Ioi
  apply (lintegral_mono (fun t ↦ h_opens _ (obs t))).trans
  refine lintegral_liminf_le ?_
  refine fun i ↦ Antitone.measurable (fun s t hst ↦ measure_mono ?_)
  intro ω hω
  simp only [Set.mem_setOf_eq] at *
  linarith

lemma main_thing
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {μs : ℕ → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    {f : Ω → ℝ} (f_cont : Continuous f) (f_nn : 0 ≤ f)
    (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
      ∫ x, (f x) ∂μ ≤ atTop.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)) := by
  sorry

lemma reduction_to_liminf {ι : Type} {L : Filter ι} [NeBot L]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μs : ι → Measure Ω} [∀ i, IsProbabilityMeasure (μs i)]
    (h : ∀ f : Ω →ᵇ ℝ, 0 ≤ f → ∫ x, (f x) ∂μ ≤ L.liminf (fun i ↦ ∫ x, (f x) ∂ (μs i)))
    (f : Ω →ᵇ ℝ) :
    Tendsto (fun i ↦ ∫ x, (f x) ∂ (μs i)) L (𝓝 (∫ x, (f x) ∂μ)) := by
  have obs := bounded_range_integral_boundedContinuousFunction_of_isProbabilityMeasure μs f
  have bdd_above : IsBoundedUnder (· ≤ ·) L (fun i ↦ ∫ (x : Ω), f x ∂μs i) := by
    apply isBounded_le_map_of_bounded_range
    apply bounded_range_integral_boundedContinuousFunction_of_isProbabilityMeasure
  have bdd_below : IsBoundedUnder (· ≥ ·) L (fun i ↦ ∫ (x : Ω), f x ∂μs i) := by
    apply isBounded_ge_map_of_bounded_range
    apply bounded_range_integral_boundedContinuousFunction_of_isProbabilityMeasure
  apply @tendsto_of_le_liminf_of_limsup_le ℝ ι _ _ _ L (fun i ↦ ∫ x, (f x) ∂ (μs i)) (∫ x, (f x) ∂μ)
  · have key := h _ (f.add_norm_nonneg)
    --have := @BoundedContinuousFunction.integral_add_const
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
  · exact L.isBounded_le_map_of_bounded_range obs
  · exact L.isBounded_ge_map_of_bounded_range obs

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
  simp_rw [integral_add (FiniteMeasure.integrable_of_boundedContinuous_to_real _ f)
                        (integrable_const ‖f‖)] at key
  simp only [integral_const, measure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul] at key
  simp_rw [fx_eq]
  convert tendsto_add.comp (Tendsto.prod_mk_nhds key (@tendsto_const_nhds _ _ _ (-‖f‖) F)) <;> simp

theorem le_liminf_open_implies_convergence
  {μ : ProbabilityMeasure Ω} {μs : ℕ → ProbabilityMeasure Ω}
  (h_opens : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i ↦ μs i G)) :
    atTop.Tendsto (fun i ↦ μs i) (𝓝 μ) := by
  refine ProbabilityMeasure.tendsto_iff_forall_nonneg_integral_tendsto.mpr ?_
  intro g g_nn
  apply reduction_to_liminf
  intro f f_nn
  have f_nn' : 0 ≤ (f : Ω → ℝ) := fun x ↦ by simpa using f_nn x
  apply main_thing f.continuous f_nn'
  -- Annoying coercions to reduce to `h_opens`...
  sorry

end le_liminf_open_implies_convergence
