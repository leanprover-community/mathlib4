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

open MeasureTheory Measure

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

variable (μ : Measure α) [Regular μ]

lemma glou {U : Set α} (hU : IsOpen U) : LowerSemicontinuousAt (fun (g : G) ↦ μ (g • U)) 1 := by
  borelize G
  intro t ht
  simp only [one_smul] at ht
  obtain ⟨K, KU, K_comp, hK⟩ : ∃ K, K ⊆ U ∧ IsCompact K ∧ t < μ K := hU.exists_lt_isCompact ht
  have : ∀ᶠ g in 𝓝 (1 : G), g • K ⊆ U := by
    obtain ⟨V, V_mem, hV⟩ :  ∃ V, V ∈ 𝓝 (1 : G) ∧ V • K ⊆ U :=
      compact_open_separated_smul G K_comp hU KU
    filter_upwards [V_mem] with g hg
    exact (smul_set_subset_smul hg).trans hV
  filter_upwards [this] with g hg
  apply hK.trans_le
  have : (g • μ) (g • K) = μ K := by simp
  rw [← this]
  exact measure_mono hg

lemma glou2 {U : Set α} (hU : IsOpen U) : LowerSemicontinuous (fun (g : G) ↦ μ (g • U)) := by
  intro g₀ t ht
  simp [smul_measure_apply] at ht
  obtain ⟨K, KU, K_comp, hK⟩ : ∃ K, K ⊆ g₀⁻¹ • U ∧ IsCompact K ∧ t < μ K :=
    (hU.smul g₀⁻¹).exists_lt_isCompact ht
  have : ∀ᶠ g in 𝓝 (1 : G), g • K ⊆ g₀⁻¹ • U := by
    obtain ⟨V, V_mem, hV⟩ :  ∃ V, V ∈ 𝓝 (1 : G) ∧ V • K ⊆ g₀⁻¹ • U :=
      compact_open_separated_smul G K_comp (hU.smul g₀⁻¹) KU
    filter_upwards [V_mem] with g hg
    exact (smul_set_subset_smul hg).trans hV
  filter_upwards [this] with g hg
  apply hK.trans_le
  have : (g • μ) (g • K) = μ K := by simp
  rw [← this]
  exact measure_mono hg




#exit


lemma glouk {U : Set α} (hU : IsOpen U) : Measurable (fun (g : G) ↦ (g • μ : Measure α) U) := by
  have Z := glou μ hU
