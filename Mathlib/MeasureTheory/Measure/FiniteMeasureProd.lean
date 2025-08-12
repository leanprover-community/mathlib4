/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Products of finite measures and probability measures

This file introduces binary products of finite measures and probability measures. The constructions
are obtained from special cases of products of general measures. Taking products nevertheless has
specific properties in the cases of finite measures and probability measures, notably the fact that
the product measures depend continuously on their factors in the topology of weak convergence when
the underlying space is metrizable and separable.

## Main definitions

* `MeasureTheory.FiniteMeasure.prod`: The product of two finite measures.
* `MeasureTheory.ProbabilityMeasure.prod`: The product of two probability measures.

## Main results

`MeasureTheory.ProbabilityMeasure.continuous_prod`: the product probability measure depends
continuously on the factors.

-/

open MeasureTheory Topology Metric Filter Set ENNReal NNReal

open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace MeasureTheory

section FiniteMeasure_product

namespace FiniteMeasure

variable {α : Type*} [MeasurableSpace α] {β : Type*} [MeasurableSpace β]

/-- The binary product of finite measures. -/
noncomputable def prod (μ : FiniteMeasure α) (ν : FiniteMeasure β) : FiniteMeasure (α × β) :=
  ⟨μ.toMeasure.prod ν.toMeasure, inferInstance⟩

variable (μ : FiniteMeasure α) (ν : FiniteMeasure β)

@[simp] lemma toMeasure_prod : (μ.prod ν).toMeasure = μ.toMeasure.prod ν.toMeasure := rfl

lemma prod_apply (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ x, ν.toMeasure (Prod.mk x ⁻¹' s) ∂μ) := by
  simp [coeFn_def, Measure.prod_apply s_mble]

lemma prod_apply_symm (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ y, μ.toMeasure ((fun x ↦ ⟨x, y⟩) ⁻¹' s) ∂ν) := by
  simp [coeFn_def, Measure.prod_apply_symm s_mble]

@[simp] lemma prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  simp [coeFn_def]

@[simp] lemma mass_prod : (μ.prod ν).mass = μ.mass * ν.mass := by
  simp only [coeFn_def, mass, univ_prod_univ.symm, toMeasure_prod]
  rw [← ENNReal.toNNReal_mul]
  exact congr_arg ENNReal.toNNReal (Measure.prod_prod univ univ)

@[simp] lemma zero_prod : (0 : FiniteMeasure α).prod ν = 0 := by
  rw [← mass_zero_iff, mass_prod, zero_mass, zero_mul]

@[simp] lemma prod_zero : μ.prod (0 : FiniteMeasure β) = 0 := by
  rw [← mass_zero_iff, mass_prod, zero_mass, mul_zero]

@[simp] lemma map_fst_prod : (μ.prod ν).map Prod.fst = ν univ • μ := by ext; simp
@[simp] lemma map_snd_prod : (μ.prod ν).map Prod.snd = μ univ • ν := by ext; simp

lemma map_prod_map {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpace β']
    {f : α → α'} {g : β → β'} (f_mble : Measurable f) (g_mble : Measurable g) :
    (μ.map f).prod (ν.map g) = (μ.prod ν).map (Prod.map f g) := by
  apply Subtype.ext
  simp only [val_eq_toMeasure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble]

lemma prod_swap : (μ.prod ν).map Prod.swap = ν.prod μ := by
  apply Subtype.ext
  simp [Measure.prod_swap]

end FiniteMeasure -- namespace

end FiniteMeasure_product -- section

section ProbabilityMeasure_product

namespace ProbabilityMeasure

variable {α : Type*} [MeasurableSpace α] {β : Type*} [MeasurableSpace β]

/-- The binary product of probability measures. -/
noncomputable def prod (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    ProbabilityMeasure (α × β) :=
  ⟨μ.toMeasure.prod ν.toMeasure, by infer_instance⟩

variable (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β)

@[simp] lemma toMeasure_prod : (μ.prod ν).toMeasure = μ.toMeasure.prod ν.toMeasure := rfl

lemma prod_apply (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ x, ν.toMeasure (Prod.mk x ⁻¹' s) ∂μ) := by
  simp [coeFn_def, Measure.prod_apply s_mble]

lemma prod_apply_symm (s : Set (α × β)) (s_mble : MeasurableSet s) :
    μ.prod ν s = ENNReal.toNNReal (∫⁻ y, μ.toMeasure ((fun x ↦ ⟨x, y⟩) ⁻¹' s) ∂ν) := by
  simp [coeFn_def, Measure.prod_apply_symm s_mble]

@[simp] lemma prod_prod (s : Set α) (t : Set β) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  simp [coeFn_def]

/-- The first marginal of a product probability measure is the first probability measure. -/
@[simp] lemma map_fst_prod : (μ.prod ν).map measurable_fst.aemeasurable = μ := by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_map, toMeasure_prod, Measure.map_fst_prod,
             measure_univ, one_smul]

/-- The second marginal of a product probability measure is the second probability measure. -/
@[simp] lemma map_snd_prod : (μ.prod ν).map measurable_snd.aemeasurable = ν := by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_map, toMeasure_prod, Measure.map_snd_prod,
             measure_univ, one_smul]

lemma map_prod_map {α' : Type*} [MeasurableSpace α'] {β' : Type*} [MeasurableSpace β']
    {f : α → α'} {g : β → β'} (f_mble : Measurable f) (g_mble : Measurable g) :
    (μ.map f_mble.aemeasurable).prod (ν.map g_mble.aemeasurable)
      = (μ.prod ν).map (f_mble.prodMap g_mble).aemeasurable := by
  apply Subtype.ext
  simp only [val_eq_to_measure, toMeasure_prod, toMeasure_map]
  rw [Measure.map_prod_map _ _ f_mble g_mble]

lemma prod_swap : (μ.prod ν).map measurable_swap.aemeasurable = ν.prod μ := by
  apply Subtype.ext
  simp [Measure.prod_swap]

open TopologicalSpace

/-- The map associating to two probability measures their product is a continuous map. -/
@[fun_prop]
theorem continuous_prod [TopologicalSpace α] [TopologicalSpace β] [SecondCountableTopology α]
    [SecondCountableTopology β] [PseudoMetrizableSpace α] [PseudoMetrizableSpace β]
    [OpensMeasurableSpace α] [OpensMeasurableSpace β] :
    Continuous (fun (μ : ProbabilityMeasure α × ProbabilityMeasure β) ↦ μ.1.prod μ.2) := by
  refine continuous_iff_continuousAt.2 (fun μ ↦ ?_)
  /- It suffices to check the convergence along elements of a π-system containing arbitrarily
  small neighborhoods of any point, by `tendsto_probabilityMeasure_of_tendsto_of_mem`.
  We take as a π-system the sets of the form `a ×ˢ b` where `a` and `b` have null frontier. -/
  let S : Set (Set (α × β)) := {t | ∃ (a : Set α) (b : Set β),
    MeasurableSet a ∧ μ.1 (frontier a) = 0 ∧ MeasurableSet b ∧ μ.2 (frontier b) = 0
    ∧ t = a ×ˢ b}
  have : IsPiSystem S := by
    rintro - ⟨a, b, ameas, ha, bmeas, hb, rfl⟩ - ⟨a', b', a'meas, ha', b'meas, hb', rfl⟩ -
    refine ⟨a ∩ a', b ∩ b', ameas.inter a'meas, ?_, bmeas.inter b'meas, ?_, prod_inter_prod⟩
    · rw [null_iff_toMeasure_null] at ha ha' ⊢
      exact null_frontier_inter ha ha'
    · rw [null_iff_toMeasure_null] at hb hb' ⊢
      exact null_frontier_inter hb hb'
  apply this.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a, b, ameas, -, bmeas, -, rfl⟩
    exact ameas.prod bmeas
  · letI : PseudoMetricSpace α := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
    letI : PseudoMetricSpace β := TopologicalSpace.pseudoMetrizableSpacePseudoMetric β
    intro u u_open x xu
    obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, ball x ε ⊆ u := Metric.isOpen_iff.1 u_open x xu
    rcases exists_null_frontier_thickening (μ.1 : Measure α) {x.1} εpos with ⟨r, hr, μr⟩
    rcases exists_null_frontier_thickening (μ.2 : Measure β) {x.2} εpos with ⟨r', hr', μr'⟩
    simp only [thickening_singleton] at μr μr'
    refine ⟨ball x.1 r ×ˢ ball x.2 r', ⟨ball x.1 r, ball x.2 r', measurableSet_ball,
      by simp [coeFn_def, μr], measurableSet_ball, by simp [coeFn_def, μr'], rfl⟩, ?_, ?_⟩
    · exact (isOpen_ball.prod isOpen_ball).mem_nhds (by simp [hr.1, hr'.1])
    · calc ball x.1 r ×ˢ ball x.2 r'
      _ ⊆ ball x.1 ε ×ˢ ball x.2 ε := by gcongr; exacts [hr.2.le, hr'.2.le]
      _ ⊆ _ := by rwa [ball_prod_same]
  · rintro s ⟨a, b, ameas, ha, bmeas, hb, rfl⟩
    simp only [prod_prod]
    apply Filter.Tendsto.mul
    · exact tendsto_measure_of_null_frontier_of_tendsto tendsto_id.fst_nhds ha
    · exact tendsto_measure_of_null_frontier_of_tendsto tendsto_id.snd_nhds hb

end ProbabilityMeasure -- namespace

end ProbabilityMeasure_product -- section

end MeasureTheory -- namespace
