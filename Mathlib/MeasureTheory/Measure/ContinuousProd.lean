import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

open MeasureTheory MeasurableSpace Measure Filter BoundedContinuousFunction
open scoped NNReal ENNReal

lemma omg {Ω₁ : Type*}
    [MeasurableSpace Ω₁] [TopologicalSpace Ω₁] [HasOuterApproxClosed Ω₁]
    [BorelSpace Ω₁] {μ : Measure Ω₁} [IsFiniteMeasure μ]
    {Ω₂ : Type*}
    [MeasurableSpace Ω₂] [TopologicalSpace Ω₂] [HasOuterApproxClosed Ω₂]
    [BorelSpace Ω₂] {ν : Measure Ω₂} [IsFiniteMeasure ν]
    {ξ : Measure (Ω₁ × Ω₂)}
    (h : ∀ (f : Ω₁ →ᵇ ℝ≥0) (g : Ω₂ →ᵇ ℝ≥0),
      ∫⁻ ω, f ω.1 * g ω.2 ∂ξ = (∫⁻ ω, f ω ∂μ) * (∫⁻ ω, g ω ∂ν)) :
    ξ = μ.prod ν := by
  let π : Set (Set (Ω₁ × Ω₂)) :=
    {s | ∃ (F : Set Ω₁) (G : Set Ω₂), IsClosed F ∧ IsClosed G ∧ s = F ×ˢ G}
  have hπ1 : IsPiSystem π := by
    rintro - ⟨s₁, s₂, hs₁, hs₂, rfl⟩ - ⟨t₁, t₂, ht₁, ht₂, rfl⟩ -
    exact ⟨s₁ ∩ t₁, s₂ ∩ t₂, hs₁.inter ht₁, hs₂.inter ht₂, Set.prod_inter_prod⟩
  have hπ2 : generateFrom π = (inferInstance : MeasurableSpace (Ω₁ × Ω₂)) := by
    rw [Prod.instMeasurableSpace, BorelSpace.measurable_eq (α := Ω₁),
      BorelSpace.measurable_eq (α := Ω₂)]
    apply le_antisymm
    · apply generateFrom_le
      rintro - ⟨s₁, s₂, hs₁, hs₂, rfl⟩
      convert hs₁.measurableSet.prod hs₂.measurableSet
      all_goals rw [← BorelSpace.measurable_eq]
    simp_rw [borel_eq_generateFrom_isClosed, MeasurableSpace.prod, comap_generateFrom]
    apply sup_le
    · apply generateFrom_le
      rintro - ⟨s, hs, rfl⟩
      apply measurableSet_generateFrom
      refine ⟨s, Set.univ, hs, isClosed_univ, ?_⟩
      rw [Set.prod_univ]
    · apply generateFrom_le
      rintro - ⟨s, hs, rfl⟩
      apply measurableSet_generateFrom
      refine ⟨Set.univ, s, isClosed_univ, hs, ?_⟩
      rw [Set.univ_prod]
  have ν_finite : IsFiniteMeasure ξ := by
    constructor
    have whole := h 1 1
    simp only [BoundedContinuousFunction.coe_one, Pi.one_apply, ENNReal.coe_one, mul_one,
      lintegral_const, one_mul] at whole
    simp [whole]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  apply ext_of_generate_finite _ hπ2.symm hπ1
  · rintro - ⟨s₁, s₂, hs₁, hs₂, rfl⟩
    rw [prod_prod]
    · have obs_μ := HasOuterApproxClosed.tendsto_lintegral_apprSeq hs₁ μ
      have obs_ν := HasOuterApproxClosed.tendsto_lintegral_apprSeq hs₂ ν
      have := ENNReal.Tendsto.mul obs_μ (by simp) obs_ν (by simp)
      symm
      apply tendsto_nhds_unique this
      simp_rw [← h, ← ENNReal.coe_mul]
      have (n : ℕ) (ω : Ω₁ × Ω₂) : hs₁.apprSeq n ω.1 * hs₂.apprSeq n ω.2 =
          (((hs₁.apprSeq n).compContinuous ⟨Prod.fst (β := Ω₂), continuous_fst⟩) *
          ((hs₂.apprSeq n).compContinuous ⟨Prod.snd (α := Ω₁), continuous_snd⟩)) ω := by
        simp
      simp_rw [this]
      simp only [BoundedContinuousFunction.coe_mul, BoundedContinuousFunction.coe_compContinuous,
        ContinuousMap.coe_mk, Pi.mul_apply, Function.comp_apply, ENNReal.coe_mul]
      have : ξ (s₁ ×ˢ s₂) = ∫⁻ ω, (s₁.indicator 1 ω.1 * s₂.indicator 1 ω.2 : ℝ≥0) ∂ξ := by
        simp_rw [← Set.indicator_prod_one]
        rw [← lintegral_indicator_one]
        · congr
          ext; simp
          rfl
        · exact hs₁.measurableSet.prod hs₂.measurableSet
      rw [this]
      apply tendsto_lintegral_filter_of_dominated_convergence (bound := 1)
      · exact Eventually.of_forall fun n ↦ by fun_prop
      · apply Eventually.of_forall
        intro n
        apply ae_of_all
        intro ω
        simp
        grw [HasOuterApproxClosed.apprSeq_apply_le_one, HasOuterApproxClosed.apprSeq_apply_le_one]
        simp
      · simp
      apply ae_of_all
      rintro ⟨ω1, ω2⟩
      simp_rw [← ENNReal.coe_mul]
      convert (ENNReal.continuous_coe.tendsto _).comp <|
        ((tendsto_pi_nhds.1 <| HasOuterApproxClosed.tendsto_apprSeq hs₁) ω1).mul
        ((tendsto_pi_nhds.1 <| HasOuterApproxClosed.tendsto_apprSeq hs₂) ω2)
  convert h 1 1
  · simp
  simp [← prod_prod]

lemma omg' {Ω₁ : Type*}
    [MeasurableSpace Ω₁] [TopologicalSpace Ω₁] [HasOuterApproxClosed Ω₁]
    [BorelSpace Ω₁] {μ : Measure Ω₁} [IsFiniteMeasure μ]
    {Ω₂ : Type*}
    [MeasurableSpace Ω₂] [TopologicalSpace Ω₂] [HasOuterApproxClosed Ω₂]
    [BorelSpace Ω₂] {ν : Measure Ω₂} [IsFiniteMeasure ν]
    {ξ : Measure (Ω₁ × Ω₂)} [IsFiniteMeasure ξ]
    (h : ∀ (f : Ω₁ →ᵇ ℝ) (g : Ω₂ →ᵇ ℝ),
      ∫ ω, f ω.1 * g ω.2 ∂ξ = (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂ν)) :
    ξ = μ.prod ν := by
  apply omg
  intro f g
  simp_rw [← ENNReal.coe_mul]
  apply (ENNReal.toReal_eq_toReal_iff' (lintegral_lt_top_of_nnreal ξ
      ((f.compContinuous ⟨Prod.fst (β := Ω₂), continuous_fst⟩) *
          (g.compContinuous ⟨Prod.snd (α := Ω₁), continuous_snd⟩))).ne
      (ENNReal.mul_lt_top (lintegral_lt_top_of_nnreal μ _) (lintegral_lt_top_of_nnreal ν _)).ne).mp
  simp only [coe_mul, coe_compContinuous, ContinuousMap.coe_mk, Pi.mul_apply, Function.comp_apply,
    ENNReal.coe_mul, ENNReal.toReal_mul]
  have : (∫⁻ ω, f ω.1 * g ω.2 ∂ξ).toReal = ∫ ω, (f ω.1).toReal * (g ω.2).toReal ∂ξ := by
    rw [integral_eq_lintegral_of_nonneg_ae]
    · simp
    · exact Eventually.of_forall fun _ ↦ by positivity
    · apply StronglyMeasurable.aestronglyMeasurable
      apply StronglyMeasurable.mul
      · change StronglyMeasurable ((fun x ↦ (f x : ℝ)) ∘ Prod.fst)
        apply StronglyMeasurable.comp_measurable
        · exact Continuous.stronglyMeasurable (by fun_prop)
        fun_prop
      · change StronglyMeasurable ((fun x ↦ (g x : ℝ)) ∘ Prod.snd)
        apply StronglyMeasurable.comp_measurable
        · exact Continuous.stronglyMeasurable (by fun_prop)
        fun_prop
  rw [this, toReal_lintegral_coe_eq_integral, toReal_lintegral_coe_eq_integral]
  exact h ⟨⟨fun x => (f x).toReal, Continuous.comp' NNReal.continuous_coe f.continuous⟩,
      f.map_bounded'⟩ ⟨⟨fun x => (g x).toReal, Continuous.comp' NNReal.continuous_coe g.continuous⟩,
      g.map_bounded'⟩
