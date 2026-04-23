/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Topology.MetricSpace.Defs
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Completely (pseudo)metrizable spaces

A topological space is completely (pseudo)metrizable if one can endow it with a
`(Pseudo)MetricSpace` structure which makes it complete and gives the same topology. This typeclass
allows to state theorems which do not require a `(Pseudo)MetricSpace` structure to make sense
without introducing such a structure.
It is in particular useful in measure theory, where one often assumes that a space is a
`PolishSpace`, i.e. a separable and completely metrizable space. Sometimes the separability
hypothesis is not needed and the right assumption is then `IsCompletelyMetrizableSpace`.

## Main definition

* `IsCompletelyPseudoMetrizableSpace X`: A topological space is completely pseudometrizable if
  there exists a pseudometric space structure compatible with the topology which makes the space
  complete. To endow such a space with a compatible distance, use
  `letI := upgradeIsCompletelyPseudoMetrizable X`.

* `IsCompletelyMetrizableSpace X`: A topological space is completely metrizable if
  there exists a metric space structure compatible with the topology which makes the space
  complete. To endow such a space with a compatible distance, use
  `letI := upgradeIsCompletelyMetrizable X`.

## Implementation note

Given a `IsCompletely(Pseudo)MetrizableSpace X` instance, one may want to endow `X` with a complete
(pseudo)metric. This can be done by writing `letI := upgradeIsCompletely(Pseudo)Metrizable X`,
which will endow `X` with an `UpgradedIsCompletely(Pseudo)MetrizableSpace X` instance. This class
is a convenience class and no instance should be registered for it.
-/

@[expose] public section

open Filter Function Set Topology

variable {X Y : Type*}

namespace TopologicalSpace

/-- A topological space is completely pseudometrizable if there exists a pseudometric space
structure compatible with the topology which makes the space complete.
To endow such a space with a compatible distance, use
`letI := upgradeIsCompletelyPseudoMetrizable X`. -/
class IsCompletelyPseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  complete : ∃ m : PseudoMetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace

instance (priority := 100) _root_.PseudoMetricSpace.toIsCompletelPseudoMetrizableSpace
    [PseudoMetricSpace X] [CompleteSpace X] : IsCompletelyPseudoMetrizableSpace X :=
  ⟨⟨‹_›, rfl, ‹_›⟩⟩

/-- A convenience class, for a completely pseudometrizable space endowed with a complete
pseudometric. No instance of this class should be registered: It should be used as
`letI := upgradeIsCompletelyPseudoMetrizable X` to endow a completely pseudometrizable
space with a complete pseudometric. -/
class UpgradedIsCompletelyPseudoMetrizableSpace (X : Type*) extends
  PseudoMetricSpace X, CompleteSpace X

open scoped Uniformity in
instance (priority := 100) IsCompletelyPseudoMetrizableSpace.of_completeSpace_pseudometrizable
    [UniformSpace X] [CompleteSpace X] [(𝓤 X).IsCountablyGenerated] :
    IsCompletelyPseudoMetrizableSpace X where
  complete := ⟨UniformSpace.pseudoMetricSpace X, rfl, ‹_›⟩

/-- Construct on a completely pseudometrizable space a pseudometric (compatible with the topology)
which is complete. -/
@[implicit_reducible]
noncomputable def completelyPseudoMetrizableMetric (X : Type*) [TopologicalSpace X]
    [h : IsCompletelyPseudoMetrizableSpace X] : PseudoMetricSpace X :=
  h.complete.choose.replaceTopology h.complete.choose_spec.1.symm

theorem complete_completelyPseudoMetrizableMetric (X : Type*) [ht : TopologicalSpace X]
    [h : IsCompletelyPseudoMetrizableSpace X] :
    @CompleteSpace X (completelyPseudoMetrizableMetric X).toUniformSpace := by
  convert h.complete.choose_spec.2
  exact PseudoMetricSpace.replaceTopology_eq _ _

/-- This definition endows a completely pseudometrizable space with a complete pseudometric.
Use it as: `letI := upgradeIsCompletelyPseudoMetrizable X`. -/
@[implicit_reducible]
noncomputable
def upgradeIsCompletelyPseudoMetrizable (X : Type*) [TopologicalSpace X]
    [IsCompletelyPseudoMetrizableSpace X] :
    UpgradedIsCompletelyPseudoMetrizableSpace X :=
  letI := completelyPseudoMetrizableMetric X
  { complete_completelyPseudoMetrizableMetric X with }

namespace IsCompletelyPseudoMetrizableSpace

/-- Note: the priority is set to 90 to ensure that this instance is only applied after
`PseudoEMetricSpace.pseudoMetrizableSpace`. This prevents unnecessary attempts to infer
completeness. -/
instance (priority := 90) PseudoMetrizableSpace [TopologicalSpace X]
    [IsCompletelyPseudoMetrizableSpace X] : PseudoMetrizableSpace X := by
  letI := upgradeIsCompletelyPseudoMetrizable X
  infer_instance

/-- A countable product of completely pseudometrizable spaces is completely pseudometrizable. -/
instance pi_countable {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, IsCompletelyPseudoMetrizableSpace (X i)] :
    IsCompletelyPseudoMetrizableSpace (Π i, X i) := by
  letI := fun i ↦ upgradeIsCompletelyPseudoMetrizable (X i)
  infer_instance

/-- The product of two completely pseudometrizable spaces is completely pseudometrizable. -/
instance prod [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X] [TopologicalSpace Y]
    [IsCompletelyPseudoMetrizableSpace Y] : IsCompletelyPseudoMetrizableSpace (X × Y) :=
  letI := upgradeIsCompletelyPseudoMetrizable X
  letI := upgradeIsCompletelyPseudoMetrizable Y
  inferInstance

/-- The disjoint union of two completely pseudometrizable spaces is completely pseudometrizable. -/
instance sum [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X] [TopologicalSpace Y]
    [IsCompletelyPseudoMetrizableSpace Y] : IsCompletelyPseudoMetrizableSpace (X ⊕ Y) :=
  letI := upgradeIsCompletelyPseudoMetrizable X
  letI := upgradeIsCompletelyPseudoMetrizable Y
  inferInstance

/-- Given a closed embedding into a completely pseudometrizable space,
the source space is also completely pseudometrizable. -/
theorem _root_.Topology.IsClosedEmbedding.IsCompletelyPseudoMetrizableSpace [TopologicalSpace X]
    [TopologicalSpace Y] [IsCompletelyPseudoMetrizableSpace Y] {f : X → Y}
    (hf : IsClosedEmbedding f) :
    IsCompletelyPseudoMetrizableSpace X := by
  letI := upgradeIsCompletelyPseudoMetrizable Y
  letI : PseudoMetricSpace X := hf.isEmbedding.comapPseudoMetricSpace
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

/-- A closed subset of a completely pseudometrizable space is also completely pseudometrizable. -/
theorem _root_.IsClosed.isCompletelyPseudoMetrizableSpace
    [TopologicalSpace X] [IsCompletelyPseudoMetrizableSpace X]
    {s : Set X} (hs : IsClosed s) : IsCompletelyPseudoMetrizableSpace s :=
  hs.isClosedEmbedding_subtypeVal.IsCompletelyPseudoMetrizableSpace

end IsCompletelyPseudoMetrizableSpace

/-- A topological space is completely metrizable if there exists a metric space structure
compatible with the topology which makes the space complete.
To endow such a space with a compatible distance, use
`letI := upgradeIsCompletelyMetrizable X`. -/
class IsCompletelyMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  complete : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t ∧
    @CompleteSpace X m.toUniformSpace

/-- A completely metrizable space is completely pseudometrizable. -/
instance IsCompletelyMetrizableSpace.toIsCompletelyPseudoMetrizableSpace [TopologicalSpace X]
    [IsCompletelyMetrizableSpace X] : IsCompletelyPseudoMetrizableSpace X := by
  obtain ⟨m, _⟩ := ‹_›
  use m.toPseudoMetricSpace

/-- A completely pseudometrizable T0 space is completely metrizable. -/
lemma IsCompletelyMetrizableSpace_of_isCompletelyPseudoMetrizableSpace [TopologicalSpace X]
    [IsCompletelyPseudoMetrizableSpace X] [T0Space X] :
    IsCompletelyMetrizableSpace X := by
  letI := upgradeIsCompletelyPseudoMetrizable X
  use MetricSpace.ofT0PseudoMetricSpace X
  exact ⟨rfl, by infer_instance⟩

instance (priority := 100) _root_.MetricSpace.toIsCompletelyMetrizableSpace
    [MetricSpace X] [CompleteSpace X] : IsCompletelyMetrizableSpace X :=
  ⟨⟨‹_›, rfl, ‹_›⟩⟩

/-- A convenience class, for a completely metrizable space endowed with a complete metric.
No instance of this class should be registered: It should be used as
`letI := upgradeIsCompletelyMetrizable X` to endow a completely metrizable
space with a complete metric. -/
class UpgradedIsCompletelyMetrizableSpace (X : Type*) extends MetricSpace X, CompleteSpace X

open scoped Uniformity in
instance (priority := 100) IsCompletelyMetrizableSpace.of_completeSpace_metrizable [UniformSpace X]
    [CompleteSpace X] [(𝓤 X).IsCountablyGenerated] [T0Space X] :
    IsCompletelyMetrizableSpace X where
  complete := ⟨UniformSpace.metricSpace X, rfl, ‹_›⟩

/-- Construct on a completely metrizable space a metric (compatible with the topology)
which is complete. -/
@[implicit_reducible]
noncomputable def completelyMetrizableMetric (X : Type*) [TopologicalSpace X]
    [h : IsCompletelyMetrizableSpace X] : MetricSpace X :=
  h.complete.choose.replaceTopology h.complete.choose_spec.1.symm

theorem complete_completelyMetrizableMetric (X : Type*) [ht : TopologicalSpace X]
    [h : IsCompletelyMetrizableSpace X] :
    @CompleteSpace X (completelyMetrizableMetric X).toUniformSpace := by
  convert h.complete.choose_spec.2
  exact MetricSpace.replaceTopology_eq _ _

/-- This definition endows a completely metrizable space with a complete metric. Use it as:
`letI := upgradeIsCompletelyMetrizable X`. -/
@[implicit_reducible]
noncomputable
def upgradeIsCompletelyMetrizable (X : Type*) [TopologicalSpace X] [IsCompletelyMetrizableSpace X] :
    UpgradedIsCompletelyMetrizableSpace X :=
  letI := completelyMetrizableMetric X
  { complete_completelyMetrizableMetric X with }

namespace IsCompletelyMetrizableSpace

/-- Note: the priority is set to 90 to ensure that this instance is only applied after
`EMetricSpace.metrizableSpace`. This prevents unnecessary attempts to infer completeness. -/
instance (priority := 90) MetrizableSpace [TopologicalSpace X] [IsCompletelyMetrizableSpace X] :
    MetrizableSpace X := by
  letI := upgradeIsCompletelyMetrizable X
  infer_instance

/-- A countable product of completely metrizable spaces is completely metrizable. -/
instance pi_countable {ι : Type*} [Countable ι] {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    [∀ i, IsCompletelyMetrizableSpace (X i)] : IsCompletelyMetrizableSpace (Π i, X i) := by
  letI := fun i ↦ upgradeIsCompletelyMetrizable (X i)
  infer_instance

/-- A disjoint union of completely metrizable spaces is completely metrizable. -/
instance sigma {ι : Type*} {X : ι → Type*} [∀ n, TopologicalSpace (X n)]
    [∀ n, IsCompletelyMetrizableSpace (X n)] : IsCompletelyMetrizableSpace (Σ n, X n) :=
  letI := fun n ↦ upgradeIsCompletelyMetrizable (X n)
  letI : MetricSpace (Σ n, X n) := Metric.Sigma.metricSpace
  haveI : CompleteSpace (Σ n, X n) := Metric.Sigma.completeSpace
  inferInstance

/-- The product of two completely metrizable spaces is completely metrizable. -/
instance prod [TopologicalSpace X] [IsCompletelyMetrizableSpace X] [TopologicalSpace Y]
    [IsCompletelyMetrizableSpace Y] : IsCompletelyMetrizableSpace (X × Y) :=
  letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  inferInstance

/-- The disjoint union of two completely metrizable spaces is completely metrizable. -/
instance sum [TopologicalSpace X] [IsCompletelyMetrizableSpace X] [TopologicalSpace Y]
    [IsCompletelyMetrizableSpace Y] : IsCompletelyMetrizableSpace (X ⊕ Y) :=
  letI := upgradeIsCompletelyMetrizable X
  letI := upgradeIsCompletelyMetrizable Y
  inferInstance

/-- Given a closed embedding into a completely metrizable space,
the source space is also completely metrizable. -/
theorem _root_.Topology.IsClosedEmbedding.IsCompletelyMetrizableSpace [TopologicalSpace X]
    [TopologicalSpace Y] [IsCompletelyMetrizableSpace Y] {f : X → Y} (hf : IsClosedEmbedding f) :
    IsCompletelyMetrizableSpace X := by
  letI := upgradeIsCompletelyMetrizable Y
  letI : MetricSpace X := hf.isEmbedding.comapMetricSpace f
  have : CompleteSpace X := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

/-- Any discrete space is completely metrizable. -/
instance (priority := 50) discrete [TopologicalSpace X] [DiscreteTopology X] :
    IsCompletelyMetrizableSpace X := by
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
    refine subset_antisymm (singleton_subset_iff.2 (Metric.mem_ball_self (by simp)))
      fun y hy ↦ ?_
    simp only [Metric.mem_ball, mem_singleton_iff] at *
    by_contra
    change (if y = x then 0 else 1) < 1 at hy
    simp_all
  · refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
    rw [Metric.cauchySeq_iff'] at hu
    obtain ⟨N, hN⟩ := hu 1 (by simp)
    refine ⟨u N, @tendsto_atTop_of_eventually_const X UniformSpace.toTopologicalSpace (u N) _ _ _ N
      fun n hn ↦ ?_⟩
    specialize hN n hn
    by_contra
    change (if u n = u N then 0 else 1) < 1 at hN
    simp_all

/-- A closed subset of a completely metrizable space is also completely metrizable. -/
theorem _root_.IsClosed.isCompletelyMetrizableSpace
    [TopologicalSpace X] [IsCompletelyMetrizableSpace X]
    {s : Set X} (hs : IsClosed s) : IsCompletelyMetrizableSpace s :=
  hs.isClosedEmbedding_subtypeVal.IsCompletelyMetrizableSpace

instance univ [TopologicalSpace X] [IsCompletelyMetrizableSpace X] :
    IsCompletelyMetrizableSpace (univ : Set X) :=
  isClosed_univ.isCompletelyMetrizableSpace

end IsCompletelyMetrizableSpace

end TopologicalSpace
