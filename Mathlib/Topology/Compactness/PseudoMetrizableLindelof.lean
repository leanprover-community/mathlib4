import Mathlib.Topology.Metrizable.Basic

variable {X : Type*} [TopologicalSpace X]

open Set Filter Topology TopologicalSpace

instance SecondCountableTopology.ofPseudoMetrizableSpaceLindelofSpace [PseudoMetrizableSpace X]
    [LindelofSpace X] : SecondCountableTopology X := by
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  have h_dense : ∀ ε > 0, ∃ s : Set X, s.Countable ∧ ∀ x, ∃ y ∈ s, dist x y ≤ ε := by
    intro ε hpos
    let U := fun (z : X) ↦ Metric.ball z ε
    have hU : ∀ z, U z ∈ 𝓝 z := by
      intro z
      have : IsOpen (U z) := Metric.isOpen_ball
      refine IsOpen.mem_nhds this ?hx
      simp only [U, Metric.mem_ball, dist_self, hpos]
    have ⟨t, hct, huniv⟩ := LindelofSpace.elim_nhds_subcover U hU
    refine ⟨t, hct, ?_⟩
    intro z
    have ⟨y, ht, hzy⟩ : ∃ y ∈ t, z ∈ U y := exists_set_mem_of_union_eq_top t (fun i ↦ U i) huniv z
    simp only [Metric.mem_ball, U] at hzy
    exact ⟨y, ht, hzy.le⟩
  exact Metric.secondCountable_of_almost_dense_set h_dense
