/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.Metrizable.Uniformity

/-!
# Completely metrizable spaces

A topological space is completely metrizable if one can endow it mith a `MetricSpace` structure
which makes it complete and gives the same topology. This typeclass allows to state theorems
which do not require a `MetricSpace` structure to make sense without introducing such a structure.
It is in particular useful in measure theory, where one often assumes that a space is a
`PolishSpace`, i.e. a separable and completely metrizable space. Sometimes the separability
hypothesis is not needed and the right assumption is then `CompletelyMetrizableSpace`.

## Main definition

* `CompletelyMetrizableSpace X`: A topological space is completely metrizable if there exists a
  metric space structure compatible with the topology which makes the space complete.
  To endow such a space with a compatible distance, use `letI := upgradeCompletelyMetrizable X`.

## Implementation note

Given a `CompletelyMetrizableSpace X` instance, one may want to endow `X` with a complete metric.
This can be done by writing `letI := upgradeCompletelyMetrizable X`, which will endow `X` with
an `UpgradedCompletelyMetrizableSpace X` instance. This class is a convenience class and
no instance should be registered for it.
-/

open Filter Function Set Topology

variable {X Y : Type*}

namespace TopologicalSpace

/-- A topological space is completely metrizable if there exists a metric space structure
compatible with the topology which makes the space complete.
To endow such a space with a compatible distance, use
`letI := upgradeCompletelyMetrizable X`. -/
class CompletelyMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  complete : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace

instance (priority := 100) _root_.MetricSpace.toCompletelyMetrizableSpace
    [MetricSpace X] [CompleteSpace X] : CompletelyMetrizableSpace X :=
  ⟨⟨‹_›, rfl, ‹_›⟩⟩

/-- A convenience class, for a completely metrizable space endowed with a complete metric.
No instance of this class should be registered: It should be used as
`letI := upgradeCompletelyMetrizable X` to endow a completely metrizable
space with a complete metric. -/
class UpgradedCompletelyMetrizableSpace (X : Type*) extends MetricSpace X, CompleteSpace X

open scoped Uniformity in
instance (priority := 100) CompletelyMetrizableSpace.of_completeSpace_metrizable [UniformSpace X]
    [CompleteSpace X] [(𝓤 X).IsCountablyGenerated] [T0Space X] :
    CompletelyMetrizableSpace X where
  complete := ⟨UniformSpace.metricSpace X, rfl, ‹_›⟩

/-- Construct on a completely metrizable space a metric (compatible with the topology)
which is complete. -/
noncomputable
def completelyMetrizableMetric (X : Type*) [TopologicalSpace X] [h : CompletelyMetrizableSpace X] :
    MetricSpace X :=
  h.complete.choose.replaceTopology h.complete.choose_spec.1.symm

theorem complete_completelyMetrizableMetric (X : Type*) [ht : TopologicalSpace X]
    [h : CompletelyMetrizableSpace X] :
    @CompleteSpace X (completelyMetrizableMetric X).toUniformSpace := by
  convert h.complete.choose_spec.2
  exact MetricSpace.replaceTopology_eq _ _

/-- This definition endows a completely metrizable space with a complete metric. Use it as:
`letI := upgradeCompletelyMetrizable X`. -/
noncomputable
def upgradeCompletelyMetrizable (X : Type*) [TopologicalSpace X] [CompletelyMetrizableSpace X] :
    UpgradedCompletelyMetrizableSpace X :=
  letI := completelyMetrizableMetric X
  { complete_completelyMetrizableMetric X with }

namespace CompletelyMetrizableSpace

instance (priority := 100) MetrizableSpace [TopologicalSpace X] [CompletelyMetrizableSpace X] :
    MetrizableSpace X := by
  letI := upgradeCompletelyMetrizable X
  infer_instance

/-- A countable product of completely metrizable spaces is completely metrizable. -/
instance pi_countable {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, CompletelyMetrizableSpace (X i)] : CompletelyMetrizableSpace (Π i, X i) := by
  letI := fun i ↦ upgradeCompletelyMetrizable (X i)
  infer_instance

/-- A disjoint union of completely metrizable spaces is completely metrizable. -/
instance sigma {ι : Type*} {X : ι → Type*} [∀ n, TopologicalSpace (X n)]
    [∀ n, CompletelyMetrizableSpace (X n)] : CompletelyMetrizableSpace (Σ n, X n) :=
  letI := fun n ↦ upgradeCompletelyMetrizable (X n)
  letI : MetricSpace (Σ n, X n) := Metric.Sigma.metricSpace
  haveI : CompleteSpace (Σ n, X n) := Metric.Sigma.completeSpace
  inferInstance

/-- The product of two completely metrizable spaces is completely metrizable. -/
instance prod [TopologicalSpace X] [CompletelyMetrizableSpace X] [TopologicalSpace Y]
    [CompletelyMetrizableSpace Y] : CompletelyMetrizableSpace (X × Y) :=
  letI := upgradeCompletelyMetrizable X
  letI := upgradeCompletelyMetrizable Y
  inferInstance

/-- The disjoint union of two completely metrizable spaces is completely metrizable. -/
instance sum [TopologicalSpace X] [CompletelyMetrizableSpace X] [TopologicalSpace Y]
    [CompletelyMetrizableSpace Y] : CompletelyMetrizableSpace (X ⊕ Y) :=
  letI := upgradeCompletelyMetrizable X
  letI := upgradeCompletelyMetrizable Y
  inferInstance

/-- Given a closed embedding into a completely metrizable space,
the source space is also completely metrizable. -/
theorem _root_.Topology.IsClosedEmbedding.CompletelyMetrizableSpace [TopologicalSpace X]
    [TopologicalSpace Y] [CompletelyMetrizableSpace Y] {f : X → Y} (hf : IsClosedEmbedding f) :
    CompletelyMetrizableSpace X := by
  letI := upgradeCompletelyMetrizable Y
  letI : MetricSpace X := hf.isEmbedding.comapMetricSpace f
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

/-- Any discrete space is completely metrizable. -/
instance (priority := 50) discrete [TopologicalSpace X] [DiscreteTopology X] :
    CompletelyMetrizableSpace X := by
  classical
  let m : MetricSpace X :=
    { dist x y := if x = y then 0 else 1
      dist_self x := by simp
      dist_comm x y := by
        obtain h | h := eq_or_ne x y
        · simp [h]
        · simp [h, h.symm]
      dist_triangle x y z := by
        by_cases x = y <;> by_cases x = z <;> by_cases y = z <;> simp_all
      eq_of_dist_eq_zero := by simp }
  refine ⟨m, ?_, ?_⟩
  · rw [DiscreteTopology.eq_bot (α := X)]
    refine eq_bot_of_singletons_open fun x ↦ ?_
    convert @Metric.isOpen_ball _ _ x 1
    refine subset_antisymm (singleton_subset_iff.2 (Metric.mem_ball_self (by norm_num)))
      fun y hy ↦ ?_
    simp only [Metric.mem_ball, mem_singleton_iff] at *
    by_contra
    change (if y = x then 0 else 1) < 1 at hy
    simp_all
  · refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
    rw [Metric.cauchySeq_iff'] at hu
    obtain ⟨N, hN⟩ := hu 1 (by norm_num)
    refine ⟨u N, @tendsto_atTop_of_eventually_const X (u N) UniformSpace.toTopologicalSpace _ _ _ N
      fun n hn ↦ ?_⟩
    specialize hN n hn
    by_contra
    change (if u n = u N then 0 else 1) < 1 at hN
    simp_all

/-- A closed subset of a completely metrizable space is also completely metrizable. -/
theorem _root_.IsClosed.CompletelyMetrizableSpace [TopologicalSpace X] [CompletelyMetrizableSpace X]
    {s : Set X} (hs : IsClosed s) : CompletelyMetrizableSpace s :=
  hs.isClosedEmbedding_subtypeVal.CompletelyMetrizableSpace

instance univ [TopologicalSpace X] [CompletelyMetrizableSpace X] :
    CompletelyMetrizableSpace (univ : Set X) :=
  isClosed_univ.CompletelyMetrizableSpace

end CompletelyMetrizableSpace

end TopologicalSpace
