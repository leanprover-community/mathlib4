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
  TopologicalSpace MeasureTheory BoundedContinuousFunction MeasureTheory.FiniteMeasure



@[simps] def CompactlySupportedContinuousMap.toBoundedContinuousFunction {α β : Type*}
    [TopologicalSpace α] [PseudoMetricSpace β] [Zero β]
    (f : C_c(α, β)) : α →ᵇ β where
  toFun := f
  map_bounded' := by
    have : IsCompact (range f) := f.hasCompactSupport.isCompact_range f.continuous
    rcases Metric.isBounded_iff.1 this.isBounded with ⟨C, hC⟩
    exact ⟨C, by grind⟩

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [T2Space E] [BorelSpace E]

variable (E) in
/-- In a compact space, the set of finite measures with mass at most `C` is compact. -/
theorem isCompact_setOf_finiteMeasure_le_of_compactSpace [CompactSpace E] (C : ℝ≥0) :
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

variable (E) in
/-- In a compact space, the set of finite measures with mass `C` is compact. -/
lemma isCompact_setOf_finiteMeasure_eq_of_compactSpace [CompactSpace E] (C : ℝ≥0) :
    IsCompact {μ : FiniteMeasure E | μ.mass = C} := by
  have : {μ : FiniteMeasure E | μ.mass = C} = {μ | μ.mass ≤ C} ∩  {μ | μ.mass = C} := by grind
  rw [this]
  apply IsCompact.inter_right (isCompact_setOf_finiteMeasure_le_of_compactSpace E C)
  exact isClosed_eq (by fun_prop) (by fun_prop)

/-- In a compact space, the space of probability measures is also compact. -/
instance [CompactSpace E] : CompactSpace (ProbabilityMeasure E) := by
  constructor
  apply (ProbabilityMeasure.toFiniteMeasure_isEmbedding E).isCompact_iff.2
  simp only [image_univ, ProbabilityMeasure.range_toFiniteMeasure]
  apply isCompact_setOf_finiteMeasure_eq_of_compactSpace

/-- The set of finite measures of mass at most `C` supported on a given compact set `K` is
compact. -/
lemma isCompact_setOf_finiteMeasure_le_of_isCompact
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [NormalSpace E] [T2Space E] [BorelSpace E]
    (C : ℝ≥0) {K : Set E} (hK : IsCompact K) :
    IsCompact {μ : FiniteMeasure E | μ.mass ≤ C ∧ μ Kᶜ = 0} := by
  let f : K → E := Subtype.val
  have hf : IsClosedEmbedding f := IsClosedEmbedding.subtypeVal hK.isClosed
  have rf : range f = K := Subtype.range_val
  let F : FiniteMeasure K → FiniteMeasure E := fun μ ↦ μ.map f
  have hF : IsEmbedding F := hK.isClosed.isClosedEmbedding_subtypeVal.isEmbedding_map_finiteMeasure
  let T : Set (FiniteMeasure K) := {μ | μ.mass ≤ C}
  have : {μ : FiniteMeasure E | μ.mass ≤ C ∧ μ Kᶜ = 0} = F '' T := by
    apply Subset.antisymm
    · intro μ hμ
      simp only [mem_image]
      refine ⟨μ.comap f, (FiniteMeasure.mass_comap_le _ _).trans hμ.1, ?_⟩
      ext s hs
      simp only [toMeasure_map, F]
      rw [Measure.map_apply measurable_subtype_coe hs]
      simp only [toMeasure_comap]
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

lemma partialSups_eq_accumulate
    {α : Type*} (f : ℕ → Set α) (n : ℕ) : partialSups f n = Accumulate f n := by
  simp [partialSups_eq_sup_range, Accumulate, Nat.lt_succ_iff]

open Measure

omit [T2Space E] [BorelSpace E]
instance innerRegular_add {μ ν : Measure E} [InnerRegular μ] [InnerRegular ν] :
    InnerRegular (μ + ν) := by
  constructor
  intro s hs r hr
  simp only [Measure.coe_add, Pi.add_apply] at hr
  rcases eq_or_ne (μ s) 0 with h | h
  · simp only [h, zero_add] at hr
    rcases MeasurableSet.exists_lt_isCompact hs hr with ⟨K, Ks, hK, h'K⟩
    exact ⟨K, Ks, hK, h'K.trans_le (by simp)⟩
  rcases eq_or_ne (ν s) 0 with h' | h'
  · simp only [h', add_zero] at hr
    rcases MeasurableSet.exists_lt_isCompact hs hr with ⟨K, Ks, hK, h'K⟩
    exact ⟨K, Ks, hK, h'K.trans_le (by simp)⟩
  rcases ENNReal.exists_lt_add_of_lt_add hr h h' with ⟨u, hu, v, hv, huv⟩
  rcases MeasurableSet.exists_lt_isCompact hs hu with ⟨K, Ks, hK, h'K⟩
  rcases MeasurableSet.exists_lt_isCompact hs hv with ⟨K', K's, hK', h'K'⟩
  refine ⟨K ∪ K', union_subset Ks K's, hK.union hK', huv.trans_le ?_⟩
  apply (add_le_add h'K.le h'K'.le).trans
  simp only [Measure.coe_add, Pi.add_apply]
  gcongr <;> simp

instance innerRegular_sum {ι : Type*} {μ : ι → Measure E} [∀ i, InnerRegular (μ i)] (a : Finset ι) :
    InnerRegular (∑ i ∈ a, μ i) := by
  classical
  induction a using Finset.induction with
  | empty => simp only [Finset.sum_empty]; infer_instance
  | insert a s ha ih => simp only [ha, not_false_eq_true, Finset.sum_insert]; infer_instance


instance {ι : Type*} {μ : ι → Measure E} [∀ i, InnerRegular (μ i)] :
    InnerRegular (Measure.sum μ) := by
  constructor
  intro s hs r hr
  have : Tendsto (fun (a : Finset ι) ↦ ∑ i ∈ a, μ i s) atTop (𝓝 (Measure.sum μ s)) := by
    simp only [hs, Measure.sum_apply]
    exact ENNReal.summable.hasSum
  obtain ⟨a, ha⟩ : ∃ (a : Finset ι), r < (∑ i ∈ a, μ i) s := by
    simp only [coe_finset_sum, Finset.sum_apply]
    exact ((tendsto_order.1 this).1 r hr).exists
  rcases MeasurableSet.exists_lt_isCompact hs ha with ⟨K, Ks, hK, h'K⟩
  refine ⟨K, Ks, hK, h'K.trans_le ?_⟩
  simp [hK.measurableSet, ENNReal.sum_le_tsum]

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
  have A n : IsCompact (partialSups K n) := by
    simpa [partialSups_eq_accumulate] using isCompact_accumulate hK _
  have M n : ∃ (ν : FiniteMeasure E), Measure.InnerRegular (ν : Measure E) ∧
      Tendsto (fun (μ : FiniteMeasure E) ↦ μ.restrict (disjointed K n)) f (𝓝 ν) := by
    obtain ⟨ν, hν, ν_lim⟩ : ∃ ν ∈ {μ : FiniteMeasure E | μ.mass ≤ C ∧ μ (partialSups K n)ᶜ = 0},
        Tendsto (fun (μ : FiniteMeasure E) ↦ μ.restrict (disjointed K n)) f (𝓝 ν) := by
      simp only [Tendsto]
      rw [← Ultrafilter.coe_map]
      apply IsCompact.ultrafilter_le_nhds'
        (isCompact_setOf_finiteMeasure_le_of_isCompact C (A n))
      simp only [null_iff_toMeasure_null, Ultrafilter.mem_map, preimage_setOf_eq]
      filter_upwards [hf] with μ hμ
      simp only [restrict_mass, restrict_measure_eq,
        Measure.restrict_apply (A n).measurableSet.compl]
      refine ⟨(apply_le_mass μ _).trans hμ.1, ?_⟩
      convert measure_empty (μ := (μ : Measure E))
      apply disjoint_iff.1
      apply disjoint_compl_left.mono_right
      exact le_trans sdiff_le (le_partialSups _ _)
    obtain ⟨ν', ν'_reg, ν'_fin, hν'⟩ : ∃ ν', ν'.InnerRegular ∧ IsFiniteMeasure ν' ∧
        ∀ (g : E →ᵇ ℝ), ∫ x, g x ∂ν = ∫ x, g x ∂ν' := by
      apply Measure.exists_innerRegular_eq_of_isCompact _ (A n)
      rw [← MeasureTheory.FiniteMeasure.null_iff_toMeasure_null]
      exact hν.2
    let μ : FiniteMeasure E := ⟨ν', ν'_fin⟩
    refine ⟨μ, ν'_reg, ?_⟩
    apply tendsto_of_forall_integral_tendsto (fun g ↦ ?_)
    convert tendsto_iff_forall_integral_tendsto.1 ν_lim g using 2
    exact (hν' g).symm
  choose! ν ν_reg hν using M
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
  have L : Tendsto id f (𝓝 μ) := by
    apply tendsto_of_forall_integral_tendsto (fun g ↦ ?_)
    rw [Metric.tendsto_nhds]
    intro ε εpos
    have : Tendsto (fun n ↦ ∫ x, g x ∂(∑ i ∈ Finset.range n, ν i)) atTop (𝓝 (∫ x, g x ∂μ)) := by
      simp only [FiniteMeasure.toMeasure_mk, μ]
      rw [integral_sum_measure (g.integrable (μ := μ))]
      simp_rw [integral_finset_sum_measure (fun i hi ↦ g.integrable _)]
      apply Summable.tendsto_sum_tsum_nat
      apply (hasSum_integral_measure _).summable
      exact g.integrable (μ := μ)
    have I1 : ∀ᶠ n in atTop,
        dist (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ν i)) (∫ x, g x ∂μ) < ε / 3 :=
      Metric.tendsto_nhds.1 (this.comp (tendsto_add_atTop_nat 1)) _ (by positivity)
    have I2 : ∀ᶠ n in atTop, ‖g‖ * u n < ε / 3 := by
      have := (NNReal.tendsto_coe.2 hu).const_mul (‖g‖)
      simp only [NNReal.coe_zero, mul_zero] at this
      exact (tendsto_order.1 this).2 (ε / 3) (by positivity)
    rcases (I1.and I2).exists with ⟨n, hn, h'n⟩
    have : Tendsto (fun (ρ : FiniteMeasure E) ↦
        ∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ρ.restrict (disjointed K i) : FiniteMeasure E)) f
        (𝓝 (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ν i : FiniteMeasure E))) := by
      apply tendsto_iff_forall_integral_tendsto.1 _ g
      apply tendsto_finset_sum _ (fun i hi ↦ hν i)
    filter_upwards [Metric.tendsto_nhds.1 this (ε / 3) (by positivity), hf] with ρ hρ h'ρ
    calc dist (∫ (x : E), g x ∂ρ) (∫ (x : E), g x ∂μ)
    _ ≤ dist (∫ (x : E), g x ∂ρ)
          (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ρ.restrict (disjointed K i)))
        + dist (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ρ.restrict (disjointed K i)))
          (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ν i))
        + dist (∫ x, g x ∂(∑ i ∈ Finset.range (n + 1), ν i)) (∫ (x : E), g x ∂μ) :=
      dist_triangle4 _ _ _ _
    _ < ε / 3 + ε / 3 + ε / 3 := by
      gcongr
      · have : ρ = ρ.restrict (partialSups K n)ᶜ +
            ∑ i ∈ Finset.range (n + 1), ρ.restrict (disjointed K i) := by
          rw [I, ← FiniteMeasure.restrict_union disjoint_compl_left (A n).measurableSet]
          simp
        nth_rewrite 1 [this]
        rw [toMeasure_add, integral_add_measure (g.integrable _) (g.integrable _)]
        simp only [toMeasure_sum, dist_add_self_left]
        calc ‖∫ x, g x ∂(ρ.restrict ((partialSups K) n)ᶜ)‖
        _ ≤ ∫ x, ‖g x‖ ∂(ρ.restrict ((partialSups K) n)ᶜ) := norm_integral_le_integral_norm _
        _ ≤ ∫ x, ‖g‖ ∂(ρ.restrict ((partialSups K) n)ᶜ : Measure E) := by
          apply integral_mono_of_nonneg
          · filter_upwards [] with x using by positivity
          · simp
          · filter_upwards [] with x using norm_coe_le_norm g x
        _ = ‖g‖ * ρ ((partialSups K) n)ᶜ := by simp [mul_comm]
        _ ≤ ‖g‖ * ρ (K n)ᶜ := by gcongr; apply le_partialSups
        _ ≤ ‖g‖ * u n := by gcongr; exact h'ρ.2 n
        _ < ε / 3 := h'n
      · simpa using hρ
    _ = ε := by ring
  refine ⟨μ, ⟨?_, fun n ↦ ?_⟩, L⟩
  · simp only [mass, mk_apply, μ]
    rw [show C = (C : ℝ≥0∞).toNNReal by simp]
    exact ENNReal.toNNReal_mono (by simp) B
  have : InnerRegular (μ : Measure E) := by simp only [toMeasure_mk, μ]; infer_instance
