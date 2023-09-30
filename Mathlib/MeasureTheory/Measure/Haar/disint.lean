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

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  {G : Type*} [TopologicalSpace G] [Group G] [MulAction G α]
  [ContinuousSMul G α]

open scoped Pointwise

lemma glou [T2Space α] (μ : Measure α) {U : Set α} (hU : IsOpen U) [Regular μ] :
    LowerSemicontinuousAt (fun (g : G) ↦ (g • μ : Measure α) U) 1 := by
  borelize G
  intro t ht
  simp only [one_smul] at ht
  obtain ⟨K, KU, K_comp, hK⟩ : ∃ K, K ⊆ U ∧ IsCompact K ∧ t < μ K := hU.exists_lt_isCompact ht
  have : ∀ᶠ g in 𝓝 (1 : G), g • K ⊆ U := by
    exact?
  filter_upwards [this] with g hg
  apply hK.trans_le
  have : (g • μ) (g • K) = μ K := by
    rw [smul_measure_def,
      Measure.map_apply (measurable_const_smul g) (IsCompact.smul g K_comp).measurableSet,
      Set.preimage_smul, smul_smul, mul_left_inv, one_smul]
  rw [← this]
  exact measure_mono hg
