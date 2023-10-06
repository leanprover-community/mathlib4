/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Un bel essai

-/

noncomputable section

open MeasureTheory Measure Filter

open scoped Topology

@[to_additive]
noncomputable instance (α : Type*) [MeasurableSpace α] (G : Type*) [SMul G α] :
    SMul G (Measure α) :=
{ smul := fun g μ ↦ Measure.map (fun x ↦ g • x) μ }

lemma smul_measure_def {α : Type*} [MeasurableSpace α] {G : Type*} [SMul G α]
    (g : G) (μ : Measure α) : g • μ = Measure.map (fun x ↦ g • x) μ := rfl

instance {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  {G : Type*} [TopologicalSpace G] [Monoid G] [MulAction G α]
  [ContinuousSMul G α] : MulAction G (Measure α) :=
{ one_smul := fun μ ↦ by simp [smul_measure_def]
  mul_smul := by
    intro g h μ
    borelize G
    simp only [smul_measure_def, ← smul_smul,
      Measure.map_map (measurable_const_smul g) (measurable_const_smul h)]
    rfl }

variable {α : Type*} [TopologicalSpace α] [T2Space α] [MeasurableSpace α] [BorelSpace α]
  {G : Type*} [TopologicalSpace G] [Group G] [MulAction G α]
  [ContinuousSMul G α]

open scoped Pointwise
open Set

lemma smul_measure_apply {μ : Measure α} (g : G) (s : Set α) : (g • μ) s = μ (g⁻¹ • s) := by
  have : MeasurableEmbedding (fun x ↦ g • x) :=
    (Homeomorph.smul g (α := α)).closedEmbedding.measurableEmbedding
  rw [smul_measure_def, MeasurableEmbedding.map_apply this, Set.preimage_smul]

@[simp]
lemma smul_measure_smul_set_eq {μ : Measure α} (g : G) (s : Set α) : (g • μ) (g • s) = μ s := by
  rw [smul_measure_apply, smul_smul, mul_left_inv, one_smul]

variable [ContinuousMul G] (μ : Measure α) [InnerRegularCompactLTTop μ]

open scoped ENNReal

lemma lowerSemicontinuous_measure_preimage [IsFiniteMeasure μ]
  {U : Set α} (hU : IsOpen U) : LowerSemicontinuous (fun (g : G) ↦ μ (g⁻¹ • U)) := by
  intro g₀ t ht
  obtain ⟨K, KU, K_comp, hK⟩ : ∃ K, K ⊆ g₀⁻¹ • U ∧ IsCompact K ∧ t < μ K :=
    MeasurableSet.exists_lt_isCompact_of_ne_top (hU.smul g₀⁻¹).measurableSet
      (measure_ne_top μ (g₀⁻¹ • U)) ht
  have A : ∀ᶠ g in 𝓝 (1 : G), g • K ⊆ g₀⁻¹ • U := by
    obtain ⟨V, V_mem, hV⟩ :  ∃ V, V ∈ 𝓝 (1 : G) ∧ V • K ⊆ g₀⁻¹ • U :=
      compact_open_separated_smul G K_comp (hU.smul g₀⁻¹) KU
    filter_upwards [V_mem] with g hg
    exact (smul_set_subset_smul hg).trans hV
  have : Tendsto (fun g ↦ g₀⁻¹ * g) (𝓝 g₀) (𝓝 (g₀⁻¹ * g₀)) :=
    tendsto_const_nhds.mul tendsto_id
  simp only [mul_left_inv] at this
  filter_upwards [this A] with g hg
  apply hK.trans_le
  apply measure_mono
  simp only [preimage_setOf_eq, mem_setOf_eq, ← smul_smul, set_smul_subset_set_smul_iff] at hg
  simpa only [subset_set_smul_iff, inv_inv] using hg

variable [MeasurableSpace G] [BorelSpace G]

lemma measurable_smul_set (g : G) {s : Set α} (hs : MeasurableSet s) :
    MeasurableSet (g • s) := by
  rw [← preimage_smul_inv]
  exact measurable_const_smul g⁻¹ hs

lemma measurable_measure_preimage_smul_of_isFiniteMeasure
    [IsFiniteMeasure μ] {s : Set α} (hs : MeasurableSet s) :
    Measurable (fun (g : G) ↦ μ (g⁻¹ • s)) := by
  apply MeasurableSet.induction_on_open (C := fun t ↦ Measurable (fun (g : G) ↦ μ (g⁻¹ • t)))
    _ _ _ hs
  · intro U hU
    exact (lowerSemicontinuous_measure_preimage μ hU).measurable
  · intro t t_meas ht
    have : ∀ (g : G), μ (g⁻¹ • tᶜ) = μ univ - μ (g⁻¹ • t) := by
      intro g
      have : g⁻¹ • tᶜ = (g⁻¹ • t)ᶜ := by simp [compl_eq_univ_diff, smul_set_sdiff]
      rw [this, measure_compl (measurable_smul_set _ t_meas) (measure_ne_top μ (g⁻¹ • t))]
    simp_rw [this]
    exact measurable_const.sub ht
  · intro f f_disj f_meas hf
    have : ∀ (g : G), μ (g⁻¹ • ⋃ n, f n) = ∑' n, μ (g ⁻¹ • f n) := by
      intro g
      rw [smul_set_Union, measure_iUnion _ (fun n ↦ measurable_smul_set _ (f_meas n))]
      exact fun m n hmn ↦ Disjoint.smul_set _ (f_disj hmn)
    simp_rw [this]
    exact Measurable.ennreal_tsum hf

instance [SigmaFinite μ] (n : ℕ) : IsFiniteMeasure (μ.restrict (spanningSets μ n)) :=
  ⟨by simpa using measure_spanningSets_lt_top μ n⟩


lemma measurable_measure_preimage_smul [SigmaFinite μ] {s : Set α} (hs : MeasurableSet s) :
    Measurable (fun (g : G) ↦ μ (g⁻¹ • s)) := by
  have : ∀ (g : G), μ (g⁻¹ • s) = ⨆ i, μ.restrict (spanningSets μ i) (g ⁻¹ • s) := by
    intro g
    rw [iSup_restrict_spanningSets]
    exact measurable_smul_set g⁻¹ hs
  simp_rw [this]
  apply measurable_iSup (fun i ↦ ?_)
  have : InnerRegularCompactLTTop (μ.restrict (spanningSets μ i)) := by
    apply InnerRegularCompactLTTop.restrict_of_measure_lt_top
    exact (measure_spanningSets_lt_top μ i).ne
  exact measurable_measure_preimage_smul_of_isFiniteMeasure _ hs
