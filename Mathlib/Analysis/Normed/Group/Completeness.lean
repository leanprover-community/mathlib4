/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Completeness of normed groups

This file includes a completeness criterion for normed additive groups in terms of convergent
series.

## Main results

* `NormedAddCommGroup.completeSpace_of_summable_imp_tendsto`: A normed additive group is
  complete if any absolutely convergent series converges in the space.

## References

* [bergh_lofstrom_1976] `NormedAddCommGroup.completeSpace_of_summable_imp_tendsto` and
  `NormedAddCommGroup.summable_imp_tendsto_of_complete` correspond to the two directions of
  Lemma 2.2.1.

## Tags

CompleteSpace, CauchySeq
-/

open scoped Topology
open Filter Finset

section Metric

variable {α : Type*} [PseudoMetricSpace α]

lemma Metric.exists_subseq_summable_dist_of_cauchySeq (u : ℕ → α) (hu : CauchySeq u) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ Summable fun i ↦ dist (u (f (i+1))) (u (f i)) := by
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_bounded_of_cauchySeq u hu
    (fun n ↦ (1 / (2 : ℝ))^n) (fun n ↦ by positivity)
  refine ⟨f, hf₁, ?_⟩
  refine Summable.of_nonneg_of_le (fun n ↦ by positivity) ?_ summable_geometric_two
  exact fun n ↦ le_of_lt <| hf₂ n (f (n + 1)) <| hf₁.monotone (Nat.le_add_right n 1)

end Metric

section Normed

variable {E : Type*} [NormedAddCommGroup E]

/-- A normed additive group is complete if any absolutely convergent series converges in the
space. -/
lemma NormedAddCommGroup.completeSpace_of_summable_imp_tendsto
    (h : ∀ u : ℕ → E,
      Summable (‖u ·‖) → ∃ a, Tendsto (fun n ↦ ∑ i ∈ range n, u i) atTop (𝓝 a)) :
    CompleteSpace E := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨f, hf₁, hf₂⟩ := Metric.exists_subseq_summable_dist_of_cauchySeq u hu
  simp only [dist_eq_norm] at hf₂
  let v n := u (f (n + 1)) - u (f n)
  have hv_sum : (fun n ↦ (∑ i ∈ range n, v i)) = fun n ↦ u (f n) - u (f 0) := by
    ext n
    exact sum_range_sub (u ∘ f) n
  obtain ⟨a, ha⟩ := h v hf₂
  refine ⟨a + u (f 0), ?_⟩
  refine tendsto_nhds_of_cauchySeq_of_subseq hu hf₁.tendsto_atTop ?_
  rw [hv_sum] at ha
  have h₁ : Tendsto (fun n ↦ u (f n) - u (f 0) + u (f 0)) atTop (𝓝 (a + u (f 0))) :=
    Tendsto.add_const _ ha
  simpa only [sub_add_cancel] using h₁

/-- In a complete normed additive group, every absolutely convergent series converges in the
space. -/
lemma NormedAddCommGroup.summable_imp_tendsto_of_complete [CompleteSpace E] (u : ℕ → E)
    (hu : Summable (‖u ·‖)) : ∃ a, Tendsto (fun n ↦ ∑ i ∈ range n, u i) atTop (𝓝 a) := by
  refine cauchySeq_tendsto_of_complete <| cauchySeq_of_summable_dist ?_
  simp [dist_eq_norm, sum_range_succ, hu]

/-- In a normed additive group, every absolutely convergent series converges in the
space iff the space is complete. -/
lemma NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace :
    (∀ u : ℕ → E, Summable (‖u ·‖) → ∃ a, Tendsto (fun n ↦ ∑ i ∈ range n, u i) atTop (𝓝 a))
     ↔ CompleteSpace E :=
  ⟨completeSpace_of_summable_imp_tendsto, fun _ u hu ↦ summable_imp_tendsto_of_complete u hu⟩

end Normed
