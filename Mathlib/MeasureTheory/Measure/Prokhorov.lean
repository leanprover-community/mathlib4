/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib

/-!
# Prokhorov theorem

-/

@[expose] public section

open scoped ENNReal NNReal
open CompactlySupported CompactlySupportedContinuousMap Filter Function Set Topology
  TopologicalSpace MeasureTheory BoundedContinuousFunction


attribute [fun_prop] FiniteMeasure.continuous_mass


@[simps] def CompactlySupportedContinuousMap.toBoundedContinuousFunction {α β : Type*}
    [TopologicalSpace α] [PseudoMetricSpace β] [Zero β]
    (f : C_c(α, β)) : α →ᵇ β where
  toFun := f
  map_bounded' := by
    have : IsCompact (range f) := f.hasCompactSupport.isCompact_range f.continuous
    rcases Metric.isBounded_iff.1 this.isBounded with ⟨C, hC⟩
    exact ⟨C, by grind⟩

@[simp] lemma FiniteMeasure.toMeasure_mk
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (h : IsFiniteMeasure μ) :
    FiniteMeasure.toMeasure (⟨μ, h⟩ : FiniteMeasure α) = μ := rfl

lemma isCompact_setOf_finiteMeasure_le_of_compactSpace (E : Type*) [MeasurableSpace E]
    [TopologicalSpace E] [T2Space E] [CompactSpace E] [BorelSpace E] (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C} := by
  /- To prove the compactness, we will show that any sequence has a converging subsequence, in
  ultrafilters terms as things are not second countable. The integral against any bounded continuous
  function has a limit along the ultrafilter, by compactness of real intervals and the mass control.
  The limit is a monotone linear form. By the Riesz-Markov-Kakutani theorem, it comes from a
  measure. This measure is finite, of mass at most `C`. It provides the desired limit
  for the ultrafilter. -/
  apply isCompact_iff_ultrafilter_le_nhds'.2 (fun f hf ↦ ?_)
  have L (g : C_c(E, ℝ)) :
      ∃ x ∈ Icc (-C * ‖g.toBoundedContinuousFunction‖) (C * ‖g.toBoundedContinuousFunction‖),
      Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ x, g x ∂ μ) f (𝓝 x) := by
    simp only [Tendsto, ← Ultrafilter.coe_map]
    apply IsCompact.ultrafilter_le_nhds' isCompact_Icc
    simp only [neg_mul, Ultrafilter.mem_map]
    filter_upwards [hf] with μ hμ
    simp only [mem_preimage, mem_Icc]
    refine ⟨?_, ?_⟩
    · calc - (C * ‖g.toBoundedContinuousFunction‖)
      _ ≤ ∫ (x : E), - ‖g.toBoundedContinuousFunction‖ ∂μ := by
        simp only [integral_const, smul_eq_mul, mul_neg, neg_le_neg_iff]
        gcongr
        exact hμ
      _ ≤ ∫ (x : E), g x ∂μ := by
        apply integral_mono
        · simp
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · intro x
          apply neg_le_of_abs_le
          exact g.toBoundedContinuousFunction.norm_coe_le_norm x
    · calc ∫ (x : E), g x ∂μ
      _ ≤ ∫ (x : E), ‖g.toBoundedContinuousFunction‖ ∂μ := by
        apply integral_mono
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · simp
        · intro x
          apply le_of_abs_le
          exact g.toBoundedContinuousFunction.norm_coe_le_norm x
      _ ≤ C * ‖g.toBoundedContinuousFunction‖ := by
        simp only [integral_const, smul_eq_mul]
        gcongr
        exact hμ
  choose Λ h₀Λ hΛ using L
  let Λ' : C_c(E, ℝ) →ₚ[ℝ] ℝ :=
  { toFun := Λ
    map_add' g g' := by
      have : Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ (x : E), g x + g' x ∂μ)
          f (𝓝 (Λ g + Λ g')) := by
        convert (hΛ g).add (hΛ g')
        rw [integral_add]
        · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
        · exact g'.continuous.integrable_of_hasCompactSupport g'.hasCompactSupport
      exact tendsto_nhds_unique (hΛ (g + g')) this
    map_smul' c g := by
      have : Tendsto (fun (μ : FiniteMeasure E) ↦ ∫ (x : E), c • g x ∂μ)
          f (𝓝 (c • Λ g)) := by
        convert (hΛ g).const_smul c
        rw [integral_smul]
      exact tendsto_nhds_unique (hΛ (c • g)) this
    monotone' g g' hgg' := by
      apply le_of_tendsto_of_tendsto' (hΛ g) (hΛ g') (fun μ ↦ ?_)
      apply integral_mono _ _ hgg'
      · exact g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
      · exact g'.continuous.integrable_of_hasCompactSupport g'.hasCompactSupport }
  let μlim := RealRMK.rieszMeasure Λ'
  have μlim_le : μlim univ ≤ ENNReal.ofReal C := by
    let o : C_c(E, ℝ) :=
    { toFun := 1
      hasCompactSupport' := HasCompactSupport.of_compactSpace 1 }
    have : μlim univ ≤ ENNReal.ofReal (Λ' o) := RealRMK.rieszMeasure_le_of_eq_one Λ'
      (fun x ↦ by simp [o]) isCompact_univ (fun x ↦ by simp [o])
    apply this.trans
    gcongr
    apply le_of_tendsto (hΛ o)
    filter_upwards [hf] with μ hμ using by simpa [o] using hμ
  let μlim' : FiniteMeasure E := ⟨μlim, ⟨μlim_le.trans_lt (by simp)⟩⟩
  refine ⟨μlim', ?_, ?_⟩
  · simp only [mem_setOf_eq, FiniteMeasure.mk_apply, μlim', FiniteMeasure.mass]
    rw [show C = (ENNReal.ofReal ↑C).toNNReal by simp]
    exact ENNReal.toNNReal_mono (by simp) μlim_le
  change Tendsto id f (𝓝 μlim')
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto (fun g ↦ ?_)
  let g' : C_c(E, ℝ) :=
  { toFun := g
    hasCompactSupport' := HasCompactSupport.of_compactSpace _ }
  convert hΛ g'
  change ∫ (x : E), g' x ∂μlim' = Λ g'
  simp only [FiniteMeasure.toMeasure_mk, RealRMK.integral_rieszMeasure, μlim', μlim]
  rfl

lemma isCompact_setOf_finiteMeasure_eq_of_compactSpace (E : Type*) [MeasurableSpace E]
    [TopologicalSpace E] [T2Space E] [CompactSpace E] [BorelSpace E] (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure E | μ.mass = C} := by
  have : {μ : FiniteMeasure E | μ.mass = C} = {μ | μ.mass ≤ C} ∩  {μ | μ.mass = C} := by grind
  rw [this]
  apply IsCompact.inter_right (isCompact_setOf_finiteMeasure_le_of_compactSpace E C)
  exact isClosed_eq (by fun_prop) (by fun_prop)

lemma isProbabilityMeasure_iff_real {α : Type*} {m : MeasurableSpace α} {μ : Measure α} :
    IsProbabilityMeasure μ ↔ μ.real univ = 1 := by
  refine ⟨fun h ↦ probReal_univ, fun h ↦ ⟨(ENNReal.toReal_eq_one_iff (μ univ)).mp h⟩⟩

@[simp] lemma FiniteMeasure.coe_real_apply {α : Type*} {m : MeasurableSpace α}
    {μ : FiniteMeasure α} {s : Set α} :
    (μ : Measure α).real s = μ s := rfl

@[simp] lemma ProbabilityMeasure.coe_real_apply {α : Type*} {m : MeasurableSpace α}
    {μ : ProbabilityMeasure α} {s : Set α} :
    (μ : Measure α).real s = μ s := rfl

@[simp] lemma ProbabilityMeasure.range_toFiniteMeasure {α : Type*} [MeasurableSpace α] :
    range (ProbabilityMeasure.toFiniteMeasure (Ω := α)) = {μ | μ.mass = 1} := by
  ext μ
  simp only [mem_range, mem_setOf_eq]
  refine ⟨fun ⟨ν, hν⟩ ↦ by simp [← hν], fun h ↦ ?_⟩
  refine ⟨⟨μ, isProbabilityMeasure_iff_real.2 (by simpa using h)⟩, ?_⟩
  ext s hs
  rfl

/-- In a compact space, the space of probability measures is also compact. -/
instance {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [CompactSpace E]
    [BorelSpace E] : CompactSpace (ProbabilityMeasure E) := by
  constructor
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding E).isCompact_iff.2
  simp only [image_univ, ProbabilityMeasure.range_toFiniteMeasure]
  apply isCompact_setOf_finiteMeasure_eq_of_compactSpace

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [MeasurableSpace α]
    [MeasurableSpace β] [BorelSpace α] [BorelSpace β]

/-- The pullback of a finite measure under a map.
If `f` is injective and sends each measurable set to a null-measurable set, then for each
measurable set `s` we have `comap f μ s = μ (f '' s)`.
Otherwise, the pullback is defined to be zero. -/
noncomputable def MeasureTheory.FiniteMeasure.comap
    (f : α → β) (μ : FiniteMeasure β) : FiniteMeasure α :=
  ⟨Measure.comap f μ, by infer_instance⟩

omit [TopologicalSpace α] [TopologicalSpace β] [BorelSpace α] [BorelSpace β] in
@[simp] lemma MeasureTheory.FiniteMeasure.coe_comap_apply
    (f : α → β) (μ : FiniteMeasure β) (s : Set α) :
    (μ.comap f : Measure α) s = (μ : Measure β).comap f s := rfl

omit [TopologicalSpace α] [TopologicalSpace β] [BorelSpace α] [BorelSpace β] in
lemma MeasureTheory.FiniteMeasure.mass_comap_le (f : α → β) (μ : FiniteMeasure β) :
    (μ.comap f).mass ≤ μ.mass := by
  simp only [mass, comap, mk_apply, coeFn_def, ne_eq, measure_ne_top, not_false_eq_true,
    ENNReal.toNNReal_le_toNNReal]
  apply (Measure.comap_apply_le _ _ nullMeasurableSet_univ).trans (measure_mono (subset_univ _))

omit [TopologicalSpace α] [TopologicalSpace β] [BorelSpace α] [BorelSpace β] in
lemma MeasureTheory.FiniteMeasure.mass_map_le (f : α → β) (μ : FiniteMeasure α) :
    (μ.map f).mass ≤ μ.mass := by
  simp only [mass, coeFn_def, toMeasure_map, ne_eq, measure_ne_top, not_false_eq_true,
    ENNReal.toNNReal_le_toNNReal]
  by_cases hf : AEMeasurable f μ
  · rw [Measure.map_apply_of_aemeasurable hf MeasurableSet.univ]
    exact measure_mono (subset_univ _)
  · simp [Measure.map_of_not_aemeasurable hf]

open MeasureTheory.FiniteMeasure

lemma Topology.IsClosedEmbedding.continuousOn_comap_finiteMeasure [NormalSpace β]
    {f : α → β} (hf : IsClosedEmbedding f) :
    ContinuousOn (fun (μ : FiniteMeasure β) ↦ μ.comap f) {μ | μ (range f)ᶜ = 0} := by
  intro μ hμ
  simp only [ContinuousWithinAt]
  rw [tendsto_iff_forall_integral_tendsto]
  intro g
  obtain ⟨g', -, hg'⟩ : ∃ g' : β →ᵇ ℝ, ‖g'‖ = ‖g‖ ∧ g' ∘ f = g :=
    exists_extension_norm_eq_of_isClosedEmbedding g hf
  have A x : g x = g' (f x) := by change (⇑g) x = (⇑g' ∘ f) x; simp only [hg']
  simp only [MeasureTheory.FiniteMeasure.comap, FiniteMeasure.toMeasure_mk, A,
    ← MeasurableEmbedding.integral_map hf.measurableEmbedding,
    MeasurableEmbedding.map_comap hf.measurableEmbedding]
  have B {ν : FiniteMeasure β} (hν : ν (range f)ᶜ = 0) :
      ∫ y in range f, g' y ∂ν = ∫ y, g' y ∂ν := by
    congr
    simp only [null_iff_toMeasure_null] at hν
    exact Measure.restrict_eq_self_of_ae_mem hν
  rw [B hμ]
  have : Tendsto (fun (ν : FiniteMeasure β) ↦ ∫ y, g' y ∂ν) (𝓝[{μ | μ (range f)ᶜ = 0}] μ)
      (𝓝 (∫ (y : β), g' y ∂μ)) := by
    rw [nhdsWithin]
    have A : Tendsto (fun (ν : FiniteMeasure β) ↦ ∫ y, g' y ∂ν) (𝓝 μ) (𝓝 (∫ (y : β), g' y ∂μ)) :=
      tendsto_iff_forall_integral_tendsto.1 tendsto_id _
    exact Tendsto.mono_left A inf_le_left
  apply Tendsto.congr' _ this
  filter_upwards [self_mem_nhdsWithin] with ν hν using (B hν).symm

attribute [fun_prop] MeasureTheory.FiniteMeasure.continuous_map

lemma Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [MeasurableSpace α]
    [MeasurableSpace β] [NormalSpace β] [BorelSpace α] [BorelSpace β]
    (f : α → β) (hf : IsClosedEmbedding f) :
    IsEmbedding (fun (μ : FiniteMeasure α) ↦ μ.map f) := by
  let M : Set (FiniteMeasure β) := {μ | μ (range f)ᶜ = 0}
  have A : IsEmbedding (Subtype.val : M → FiniteMeasure β) := IsEmbedding.subtypeVal
  let B : FiniteMeasure α ≃ₜ M :=
  { toFun μ := by
      refine ⟨μ.map f, ?_⟩
      simp only [null_iff_toMeasure_null, mem_setOf_eq, toMeasure_map, M]
      rw [Measure.map_apply hf.continuous.measurable hf.isClosed_range.isOpen_compl.measurableSet]
      simp
    invFun := M.restrict (fun μ ↦ μ.comap f)
    continuous_toFun := by fun_prop
    continuous_invFun := by
      rw [← continuousOn_iff_continuous_restrict]
      exact hf.continuousOn_comap_finiteMeasure
    left_inv μ := by
      ext s hs
      simp only [Set.restrict_apply, coe_comap_apply, toMeasure_map]
      rw [Measure.comap_apply, Measure.map_apply, preimage_image_eq]
      · exact hf.injective
      · exact hf.continuous.measurable
      · exact hf.measurableEmbedding.measurableSet_image' hs
      · exact hf.injective
      · exact fun t ht ↦ hf.measurableEmbedding.measurableSet_image' ht
      · exact hs
    right_inv μ := by
      ext s hs
      simp only [Set.restrict_apply, toMeasure_map]
      rw [Measure.map_apply hf.continuous.measurable hs]
      simp only [coe_comap_apply]
      rw [Measure.comap_apply _ hf.injective, image_preimage_eq_inter_range]
      · rw [← Measure.restrict_apply hs, Measure.restrict_eq_self_of_ae_mem]
        exact (null_iff_toMeasure_null (↑μ) (range f)ᶜ).mp (by exact μ.2)
      · exact fun t ht ↦ hf.measurableEmbedding.measurableSet_image' ht
      · exact hf.continuous.measurable hs }
  exact A.comp B.isEmbedding

lemma isCompact_setOf_finiteMeasure_le_of_isCompact
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [NormalSpace E] [T2Space E] [BorelSpace E]
    (C : ℝ≥0) {K : Set E} (hK : IsCompact K) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C ∧ μ Kᶜ = 0} := by
  let f : K → E := Subtype.val
  have hf : IsClosedEmbedding f := IsClosedEmbedding.subtypeVal hK.isClosed
  have rf : range f = K := Subtype.range_val
  let F : FiniteMeasure K → FiniteMeasure E := fun μ ↦ μ.map f
  have hF : IsEmbedding F := by
    apply Topology.IsClosedEmbedding.isEmbedding_map_finiteMeasure
    exact hK.isClosed.isClosedEmbedding_subtypeVal
  let T : Set (FiniteMeasure K) := {μ | μ.mass ≤ C}
  have : {μ : FiniteMeasure E | μ.mass ≤ C ∧ μ Kᶜ = 0} = F '' T := by
    apply Subset.antisymm
    · intro μ hμ
      simp only [mem_image]
      refine ⟨μ.comap f, (FiniteMeasure.mass_comap_le _ _).trans hμ.1, ?_⟩
      ext s hs
      simp only [toMeasure_map, F]
      rw [Measure.map_apply measurable_subtype_coe hs]
      simp only [coe_comap_apply]
      rw [Measure.comap_apply _ (Subtype.val_injective), image_preimage_eq_inter_range]
      · rw [← Measure.restrict_apply hs, Measure.restrict_eq_self_of_ae_mem]
        apply (null_iff_toMeasure_null (↑μ) (range f)ᶜ).mp
        rw [rf]
        exact hμ.2
      · exact fun t ht ↦ hf.measurableEmbedding.measurableSet_image' ht
      · exact hf.continuous.measurable hs
    · simp only [null_iff_toMeasure_null, image_subset_iff, preimage_setOf_eq, toMeasure_map,
        setOf_subset_setOf, F, T]
      intro μ hμ
      rw [Measure.map_apply hf.continuous.measurable hK.measurableSet.compl]
      refine ⟨(mass_map_le _ _).trans hμ, by simp [f]⟩
  rw [this, ← hF.isCompact_iff]
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact isCompact_setOf_finiteMeasure_le_of_compactSpace _ _

omit [TopologicalSpace α] [BorelSpace α] in
@[simp] theorem toMeasure_sum {ι : Type*} {s : Finset ι} {ν : ι → FiniteMeasure α} :
    ↑(∑ i ∈ s, ν i) = ∑ i ∈ s, (ν i : Measure α) :=
  map_sum toMeasureAddMonoidHom _ _

instance : ContinuousAdd (FiniteMeasure α) := by
  refine ⟨continuous_iff_continuousAt.2 (fun p ↦ ?_)⟩
  apply tendsto_iff_forall_lintegral_tendsto.2 (fun g ↦ ?_)
  have A : Tendsto (fun (i : FiniteMeasure α × FiniteMeasure α) ↦ ∫⁻ x, g x ∂i.1) (𝓝 p)
      (𝓝 (∫⁻ x, g x ∂p.1)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_lintegral_tendsto.1 tendsto_id g).comp tendsto_fst
  have B : Tendsto (fun (i : FiniteMeasure α × FiniteMeasure α) ↦ ∫⁻ x, g x ∂i.2) (𝓝 p)
      (𝓝 (∫⁻ x, g x ∂p.2)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_lintegral_tendsto.1 tendsto_id g).comp tendsto_snd
  convert A.add B with q <;> simp

instance : ContinuousSMul ℝ≥0 (FiniteMeasure α) := by
  refine ⟨continuous_iff_continuousAt.2 (fun p ↦ ?_)⟩
  apply tendsto_iff_forall_integral_tendsto.2 (fun g ↦ ?_)
  have A : Tendsto (fun (i : ℝ≥0 × FiniteMeasure α) ↦ i.1) (𝓝 p) (𝓝 (p.1)) := by
    rw [nhds_prod_eq]
    exact tendsto_fst
  have B : Tendsto (fun (i : ℝ≥0 × FiniteMeasure α) ↦ ∫ x, g x ∂i.2) (𝓝 p)
      (𝓝 (∫ x, g x ∂p.2)) := by
    rw [nhds_prod_eq]
    exact (tendsto_iff_forall_integral_tendsto.1 tendsto_id g).comp tendsto_snd
  convert A.smul B with q <;> simp

omit [TopologicalSpace α] [BorelSpace α] in
lemma FiniteMeasure.restrict_union
    {μ : FiniteMeasure α} {s t : Set α} (h : Disjoint s t) (ht : MeasurableSet t) :
    μ.restrict (s ∪ t) = μ.restrict s + μ.restrict t := by
  ext u hu
  simp [restrict_measure_eq, Measure.restrict_union h ht]

omit [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] in
lemma partialSups_add_one_eq_sup_disjointed {ι : Type*} [GeneralizedBooleanAlgebra α]
    [LinearOrder ι] [Add ι] [One ι] [LocallyFiniteOrderBot ι] [SuccAddOrder ι]
    (f : ι → α) (i : ι) : partialSups f (i + 1) = partialSups f i ⊔ disjointed f (i + 1) := by
  by_cases hi : IsMax i
  · have : i + 1 = i := by
      have h : i ≤ i + 1 := by
        rw [← Order.succ_eq_add_one]
        apply Order.le_succ
      exact le_antisymm (hi h) h
    simp only [this, left_eq_sup, ge_iff_le, disjointed, sdiff_le_iff]
    apply le_trans (le_partialSups_of_le _ le_rfl) le_sup_right
  · rw [← Order.succ_eq_add_one, disjointed_succ _ hi]
    simp

lemma partialSups_eq_accumulate
    {α : Type*} (f : ℕ → Set α) (n : ℕ) : partialSups f n = Accumulate f n := by
  simp [partialSups_eq_sup_range, Accumulate, Nat.lt_succ_iff]

#check Metric.tendsto_nhds

lemma prokh_aux' {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [T2Space E] [NormalSpace E] [BorelSpace E] {u : ℕ → ℝ≥0} {K : ℕ → Set E}
    (C : ℝ≥0) (hu : Tendsto u atTop (𝓝 0)) (hK : ∀ n, IsCompact (K n)) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C ∧ ∀ n, μ (K n)ᶜ ≤ u n} := by
  have I (μ : FiniteMeasure E) (n : ℕ) :
        ∑ i ∈ Finset.range (n + 1), μ.restrict (disjointed K i) = μ.restrict (partialSups K n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Finset.sum_range_succ, ih]
      rw [← FiniteMeasure.restrict_union]
      · simp only [partialSups_add_one_eq_sup_disjointed, sup_eq_union]
      · rw [← Order.succ_eq_add_one, disjointed_succ _ (not_isMax n)]
        exact disjoint_sdiff_right
      · apply MeasurableSet.disjointed (fun i ↦ (hK i).measurableSet)
  apply isCompact_iff_ultrafilter_le_nhds'.2 (fun f hf ↦ ?_)
  have M n : ∃ ν ∈ {μ : FiniteMeasure E | μ.mass ≤ C ∧ μ (partialSups K n)ᶜ = 0},
      Tendsto (fun (μ : FiniteMeasure E) ↦ μ.restrict (disjointed K n)) f (𝓝 ν) := by
    simp only [Tendsto]
    rw [← Ultrafilter.coe_map]
    have A : IsCompact (partialSups K n) := by
      simpa [partialSups_eq_accumulate] using isCompact_accumulate hK _
    apply IsCompact.ultrafilter_le_nhds'
      (isCompact_setOf_finiteMeasure_le_of_isCompact C A)
    simp only [null_iff_toMeasure_null, Ultrafilter.mem_map, preimage_setOf_eq]
    filter_upwards [hf] with μ hμ
    simp only [restrict_mass, restrict_measure_eq,
      Measure.restrict_apply A.measurableSet.compl]
    refine ⟨(apply_le_mass μ _).trans hμ.1, ?_⟩
    convert measure_empty (μ := (μ : Measure E))
    apply disjoint_iff.1
    apply disjoint_compl_left.mono_right
    exact le_trans sdiff_le (le_partialSups_of_le _ le_rfl)
  choose! ν ν_mem hν using M
  have B : (Measure.sum (fun n ↦ (ν n : Measure E))) univ ≤ C := by
    simp only [MeasurableSet.univ, Measure.sum_apply]
    have : Tendsto (fun n ↦ ∑ i ∈ Finset.range (n + 1), (ν i : Measure E) univ) atTop
        (𝓝 (∑' i, (ν i : Measure E) univ)) :=
      (ENNReal.tendsto_nat_tsum _).comp (tendsto_add_atTop_nat 1)
    apply le_of_tendsto' this (fun n ↦ ?_)
    have : ∑ i ∈ Finset.range (n + 1), (ν i : Measure E) univ
        = (∑ i ∈ Finset.range (n + 1), ν i).toMeasure univ := by
      simp only [toMeasure_sum, Measure.coe_finset_sum, Finset.sum_apply]
    rw [this]
    suffices (∑ i ∈ Finset.range (n + 1), ν i).mass ≤ C by
      convert ENNReal.coe_le_coe.2 this
      simp
    have : Tendsto (fun (μ : FiniteMeasure E) ↦
        (∑ i ∈ Finset.range (n + 1), μ.restrict (disjointed K i)).mass) f
        (𝓝 ((∑ i ∈ Finset.range (n + 1), ν i).mass)) := by
      apply Tendsto.mass
      exact tendsto_finset_sum _ (fun i hi ↦ hν i)
    apply le_of_tendsto this
    filter_upwards [hf] with μ hμ
    rw [I, restrict_mass]
    exact le_trans (apply_mono _ (subset_univ _)) hμ.1
  let μ : FiniteMeasure E := ⟨Measure.sum (fun n ↦ (ν n : Measure E)), ⟨B.trans_lt (by simp)⟩⟩
  refine ⟨μ, ⟨?_, ?_⟩, ?_⟩
  · simp only [mass, mk_apply, μ]
    rw [show C = (C : ℝ≥0∞).toNNReal by simp]
    exact ENNReal.toNNReal_mono (by simp) B
  · sorry
  · change Tendsto id f (𝓝 μ)
    apply tendsto_of_forall_integral_tendsto (fun g ↦ ?_)
    rw [Metric.tendsto_nhds]
    intro ε εpos
    have A : Tendsto (fun n ↦ ∫ x, g x ∂(∑ i ∈ Finset.range n, ν i)) atTop (𝓝 (∫ x, g x ∂μ)) := by
      simp only [FiniteMeasure.toMeasure_mk, μ]
      rw [integral_sum_measure (g.integrable (μ := μ))]
      simp_rw [integral_finset_sum_measure (fun i hi ↦ g.integrable (μ := ν i))]
      apply Summable.tendsto_sum_tsum_nat
      apply (hasSum_integral_measure _).summable
      exact g.integrable (μ := μ)
    have I1 : ∀ᶠ n in atTop, dist (∫ x, g x ∂(∑ i ∈ Finset.range n, ν i)) (∫ x, g x ∂μ) < ε / 3 :=
      Metric.tendsto_nhds.1 A _ (by positivity)
    have I2 : ∀ᶠ n in atTop, ‖g‖ * u n < ε / 3 := by
      have := (NNReal.tendsto_coe.2 hu).const_mul (‖g‖)
      simp only [NNReal.coe_zero, mul_zero] at this
      exact (tendsto_order.1 this).2 (ε / 3) (by positivity)
    rcases (I1.and I2).exists with ⟨n, hn⟩
    have : Tendsto (fun (ρ : FiniteMeasure E) ↦
        ∫ x, g x ∂(∑ i ∈ Finset.range n, ρ.restrict (disjointed K i) : FiniteMeasure E)) f
        (𝓝 (∫ x, g x ∂(∑ i ∈ Finset.range n, ν i : FiniteMeasure E))) := by
      apply tendsto_iff_forall_integral_tendsto.1 _ g
      apply tendsto_finset_sum _ (fun i hi ↦ hν i)
    filter_upwards [Metric.tendsto_nhds.1 this (ε / 3) (by positivity)] with ρ hρ












#exit
