/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# AuxLemmas
-/

open MeasureTheory
open scoped ENNReal NNReal

--PRed
lemma ENNReal.add_sub_add_eq_sub_right {a c b : ℝ≥0∞} (hc : c ≠ ∞) :
    (a + c) - (b + c) = a - b := by
  lift c to ℝ≥0 using hc
  cases a <;> cases b
  · simp
  · simp
  · simp
  · norm_cast
    rw [add_tsub_add_eq_tsub_right]

--PRed
lemma ENNReal.add_sub_add_eq_sub_left {a c b : ℝ≥0∞} (hc : c ≠ ∞) :
    (c + a) - (c + b) = a - b := by
  simp_rw [add_comm c]
  exact ENNReal.add_sub_add_eq_sub_right hc

-- from BrownianMotion
theorem Set.Finite.lt_iInf_iff {α ι : Type*} [CompleteLinearOrder α]
    {s : Set ι} {f : ι → α} (h : s.Nonempty) (hs : s.Finite) {a : α} :
    a < ⨅ i ∈ s, f i ↔ ∀ x ∈ s, a < f x := sorry

lemma iInf_eq_bot_iff_of_finite {α ι : Type*} [CompleteLinearOrder α] [Finite ι] [Nonempty ι]
    {f : ι → α} : (⨅ i, f i) = ⊥ ↔ ∃ i, f i = ⊥ := by
  refine ⟨fun h ↦ ?_, fun ⟨i, hi⟩ ↦ le_antisymm ((iInf_le _ i).trans_eq hi) bot_le⟩
  by_contra! h'
  simp_rw [← bot_lt_iff_ne_bot] at h'
  have h'' : ∀ i ∈ (Set.univ : Set ι), ⊥ < f i := by simpa
  rw [← Set.Finite.lt_iInf_iff (by simp) Set.finite_univ] at h''
  simp only [Set.mem_univ, iInf_pos] at h''
  exact h''.ne' h

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

--PRed
lemma Measure.eq_of_le_of_measure_univ_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≤ ν) (h_univ : μ .univ = ν .univ) : μ = ν := by
  ext s hs
  refine le_antisymm (hμν s) ?_
  by_contra! h_lt
  have : Set.univ = s ∪ sᶜ := by simp
  have h_disj : Disjoint s sᶜ := Set.disjoint_compl_right_iff_subset.mpr subset_rfl
  replace h_univ : ν .univ ≤ μ .univ := h_univ.symm.le
  rw [this, measure_union h_disj hs.compl, measure_union h_disj hs.compl] at h_univ
  refine absurd h_univ ?_
  push_neg
  refine ENNReal.add_lt_add_of_lt_of_le (by finiteness) h_lt (hμν sᶜ)

--PRed
lemma Measure.eq_of_le_of_isProbabilityMeasure [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≤ ν) : μ = ν :=
  eq_of_le_of_measure_univ_eq hμν (by simp)

end MeasureTheory

lemma measurable_encode {α : Type*} {_ : MeasurableSpace α} [Encodable α]
    [MeasurableSingletonClass α] :
    Measurable (Encodable.encode (α := α)) := by
  refine measurable_to_nat fun a ↦ ?_
  have : Encodable.encode ⁻¹' {Encodable.encode a} = {a} := by ext; simp
  rw [this]
  exact measurableSet_singleton _

lemma measurableEmbedding_encode (α : Type*) {_ : MeasurableSpace α} [Encodable α]
    [MeasurableSingletonClass α] :
    MeasurableEmbedding (Encodable.encode (α := α)) where
  injective := Encodable.encode_injective
  measurable := measurable_encode
  measurableSet_image' _ _ := .of_discrete
