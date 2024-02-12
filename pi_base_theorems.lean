import Mathlib

/- The point of this file is to track all theorems in Pi-Base, the dictionary of basic results and
spaces in general topology. Each result should be a simple #synthesize call. -/


/- T1 : Compact implies countably compact -/
-- definition of CountablyCompactSpace missing
-- also makes T2 - T4 impossible

/- T5: Exhaustible by compacts implies Hemicompact -/
-- definition of Exhaustible by compacts missing (σ-compact and weakly locally compact)
-- definition hemicompact missing

/- T6 - T9 : Definitions missing -/

/- T10 : Extremally disconnected and Metrizable implies Discrete -/
variable {α : Type*} [MetricSpace α] [ExtremallyDisconnected α]
#synth DiscreteTopology α

example {α : Type*} [MetricSpace α] [ExtremallyDisconnected α] : DiscreteTopology α := by
  refine singletons_open_iff_discrete.mp ?_
  by_contra h
  push_neg at h
  have ⟨s, hs⟩ := h
  let U := ⋃ n : ℕ, (Metric.ball s (1/(2*n))) \ (Metric.ball s (1/(2*n)))
  have hU : IsOpen U := by
    simp_all only [one_div, mul_inv_rev, sdiff_self, Set.bot_eq_empty, Set.iUnion_empty, isOpen_empty]
  sorry

/- T11 : Definition missing -/

/- T12 : Fully T4 implies Paracompact, relies on T11 -/
variable {α : Type*} [TopologicalSpace α] [T4Space α]
#synth ParacompactSpace α

/- T13 : Compact implies paracompact-/
variable {α : Type*} [TopologicalSpace α] [CompactSpace α]
#synth ParacompactSpace α

/- T14 : Paracompact implies metacompact-/
variable {α : Type*} [TopologicalSpace α] [ParacompactSpace α]
#synth MetacompactSpace α
