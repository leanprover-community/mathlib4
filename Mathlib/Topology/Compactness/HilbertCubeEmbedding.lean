/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Topology.UnitInterval

/-!
# Any compact metric space can be embedded into the Hilbert cube.

In this file we prove `exists_closed_embedding_to_hilbert`: any compact metric space can be embedded
into the Hilbert cube (`ℕ → unitInterval`).
-/

open Classical in
/-- Any compact metric space can be embedded into the Hilbert cube. -/
theorem exists_closed_embedding_to_hilbert_cube (X : Type*) [MetricSpace X] [CompactSpace X] :
    ∃ f : X → (ℕ → unitInterval), Topology.IsClosedEmbedding f := by
  let f : X → (ℕ → unitInterval) :=
    if h : Nonempty X then
      let s := TopologicalSpace.denseSeq X
      fun x i =>
        let d := dist x (s i)
        let diam := Metric.diam (Set.univ : Set X)
        have hd1 : d ≤ diam := by
          simp [diam]
          apply Metric.dist_le_diam_of_mem
          · rwa [← Metric.compactSpace_iff_isBounded_univ]
          · simp
          · simp
        have hd2 : (d / diam) ∈ unitInterval := by
          simp only [Set.mem_Icc, diam]
          constructor
          · positivity
          · apply div_le_one_of_le₀ hd1
            positivity
        ⟨_, hd2⟩
    else
      fun x i ↦ 0
  use f
  apply Continuous.isClosedEmbedding
  · simp only [f]
    split_ifs <;> fun_prop
  intro x y hxy
  simp only [f] at hxy
  split_ifs at hxy with h
  swap
  · simp at h
    exfalso
    exact h.false x
  suffices dist x y = 0 from eq_of_dist_eq_zero this
  simp only [f] at hxy
  apply congrFun at hxy
  simp only [Subtype.mk.injEq, f] at hxy
  set diam := Metric.diam (Set.univ : Set X)
  by_cases h_diam : diam = 0
  · have : dist x y ≤ diam := by
      apply Metric.dist_le_diam_of_mem (by rwa [← Metric.compactSpace_iff_isBounded_univ]) <;> simp
    linarith [dist_nonneg (x := x) (y := y)]
  simp_rw [div_left_inj' h_diam] at hxy
  have h_dense := TopologicalSpace.denseRange_denseSeq X
  simp only [DenseRange, f] at h_dense
  by_contra! h
  set s := TopologicalSpace.denseSeq X
  obtain ⟨i, hx⟩ : ∃ i, dist x (s i) < dist x y / 3 := by
    simpa using h_dense.exists_dist_lt x (ε := dist x y / 3) (by positivity)
  have hy : dist (s i) y < dist x y / 3 := by
    rwa [dist_comm, ← hxy]
  have := dist_triangle x (s i) y
  linarith [dist_nonneg (x := x) (y := y)]
