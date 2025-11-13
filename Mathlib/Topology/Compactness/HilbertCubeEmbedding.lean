/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Topology.UnitInterval

/-!
# Every compact metric space can be embedded into the Hilbert cube.

In this file we prove `exists_closed_embedding_to_hilbert`: every compact metric space can be
embedded into the Hilbert cube (`ℕ → unitInterval`).
-/

/-- Every compact metric space can be embedded into the Hilbert cube. -/
theorem exists_closed_embedding_to_hilbert_cube (X : Type*) [MetricSpace X] [CompactSpace X] :
    ∃ f : X → (ℕ → unitInterval), Topology.IsClosedEmbedding f := by
  obtain _ | _ := subsingleton_or_nontrivial X
  · use Function.const _ 0
    exact continuous_const.isClosedEmbedding <| Function.injective_of_subsingleton _
  let s := TopologicalSpace.denseSeq X
  have s_dense : DenseRange s := TopologicalSpace.denseRange_denseSeq X
  let diam := Metric.diam (Set.univ : Set X)
  have dist_le_diam : ∀ x y, dist x y ≤ diam :=
    fun x y ↦ Metric.dist_le_diam_of_mem isCompact_univ.isBounded trivial trivial
  have diam_pos : 0 < diam :=
    Metric.diam_pos (by rwa [Set.nontrivial_univ_iff]) isCompact_univ.isBounded
  let f : X → (ℕ → unitInterval) := fun x i =>
    ⟨dist x (s i) / diam, by positivity, div_le_one_of_le₀ (dist_le_diam _ _) Metric.diam_nonneg⟩
  use f
  apply Continuous.isClosedEmbedding
  · fun_prop
  intro x y hxy
  simp only [f] at hxy
  suffices dist x y = 0 from eq_of_dist_eq_zero this
  suffices dist x = dist y from dist_self y ▸ congrFun this y
  apply s_dense.equalizer (by fun_prop) (by fun_prop)
  ext i
  rw [← div_left_inj' diam_pos.ne']
  exact congr(((↑) : unitInterval → ℝ) ($hxy i))
