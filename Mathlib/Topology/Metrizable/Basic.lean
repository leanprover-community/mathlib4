/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.MetricSpace.Basic

/-!
# Metrizability of a T₃ topological space with second countable topology

In this file we define metrizable topological spaces, i.e., topological spaces for which there
exists a metric space structure that generates the same topology.
-/

open Filter Set Metric Topology

namespace TopologicalSpace

variable {ι X Y : Type*} {π : ι → Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
  [∀ i, TopologicalSpace (π i)]

/-- A topological space is *pseudo metrizable* if there exists a pseudo metric space structure
compatible with the topology. To endow such a space with a compatible distance, use
`letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X`. -/
class PseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_pseudo_metric : ∃ m : PseudoMetricSpace X, m.toUniformSpace.toTopologicalSpace = t

instance (priority := 100) _root_.PseudoMetricSpace.toPseudoMetrizableSpace {X : Type*}
    [m : PseudoMetricSpace X] : PseudoMetrizableSpace X :=
  ⟨⟨m, rfl⟩⟩

/-- Construct on a metrizable space a metric compatible with the topology. -/
noncomputable def pseudoMetrizableSpacePseudoMetric (X : Type*) [TopologicalSpace X]
    [h : PseudoMetrizableSpace X] : PseudoMetricSpace X :=
  h.exists_pseudo_metric.choose.replaceTopology h.exists_pseudo_metric.choose_spec.symm

instance pseudoMetrizableSpace_prod [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y] :
    PseudoMetrizableSpace (X × Y) :=
  letI : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  letI : PseudoMetricSpace Y := pseudoMetrizableSpacePseudoMetric Y
  inferInstance

/-- Given an inducing map of a topological space into a pseudo metrizable space, the source space
is also pseudo metrizable. -/
theorem _root_.Topology.IsInducing.pseudoMetrizableSpace [PseudoMetrizableSpace Y] {f : X → Y}
    (hf : IsInducing f) : PseudoMetrizableSpace X :=
  letI : PseudoMetricSpace Y := pseudoMetrizableSpacePseudoMetric Y
  ⟨⟨hf.comapPseudoMetricSpace, rfl⟩⟩

@[deprecated (since := "2024-10-28")]
alias _root_.Inducing.pseudoMetrizableSpace := IsInducing.pseudoMetrizableSpace

/-- Every pseudo-metrizable space is first countable. -/
instance (priority := 100) PseudoMetrizableSpace.firstCountableTopology
    [h : PseudoMetrizableSpace X] : FirstCountableTopology X := by
  rcases h with ⟨_, hm⟩
  rw [← hm]
  exact @UniformSpace.firstCountableTopology X PseudoMetricSpace.toUniformSpace
    EMetric.instIsCountablyGeneratedUniformity

instance PseudoMetrizableSpace.subtype [PseudoMetrizableSpace X] (s : Set X) :
    PseudoMetrizableSpace s :=
  IsInducing.subtypeVal.pseudoMetrizableSpace

instance pseudoMetrizableSpace_pi [∀ i, PseudoMetrizableSpace (π i)] :
    PseudoMetrizableSpace (∀ i, π i) := by
  cases nonempty_fintype ι
  letI := fun i => pseudoMetrizableSpacePseudoMetric (π i)
  infer_instance

/-- A topological space is metrizable if there exists a metric space structure compatible with the
topology. To endow such a space with a compatible distance, use
`letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X`. -/
class MetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_metric : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t

instance (priority := 100) _root_.MetricSpace.toMetrizableSpace {X : Type*} [m : MetricSpace X] :
    MetrizableSpace X :=
  ⟨⟨m, rfl⟩⟩

instance (priority := 100) MetrizableSpace.toPseudoMetrizableSpace [h : MetrizableSpace X] :
    PseudoMetrizableSpace X :=
  let ⟨m, hm⟩ := h.1
  ⟨⟨m.toPseudoMetricSpace, hm⟩⟩

instance (priority := 100) PseudoMetrizableSpace.toMetrizableSpace
    [T0Space X] [h : PseudoMetrizableSpace X] : MetrizableSpace X :=
  letI := pseudoMetrizableSpacePseudoMetric X
  ⟨.ofT0PseudoMetricSpace X, rfl⟩

/-- Construct on a metrizable space a metric compatible with the topology. -/
noncomputable def metrizableSpaceMetric (X : Type*) [TopologicalSpace X] [h : MetrizableSpace X] :
    MetricSpace X :=
  h.exists_metric.choose.replaceTopology h.exists_metric.choose_spec.symm

instance (priority := 100) t2Space_of_metrizableSpace [MetrizableSpace X] : T2Space X :=
  letI : MetricSpace X := metrizableSpaceMetric X
  inferInstance

instance metrizableSpace_prod [MetrizableSpace X] [MetrizableSpace Y] : MetrizableSpace (X × Y) :=
  letI : MetricSpace X := metrizableSpaceMetric X
  letI : MetricSpace Y := metrizableSpaceMetric Y
  inferInstance

/-- Given an embedding of a topological space into a metrizable space, the source space is also
metrizable. -/
theorem _root_.Topology.IsEmbedding.metrizableSpace [MetrizableSpace Y] {f : X → Y}
    (hf : IsEmbedding f) : MetrizableSpace X :=
  letI : MetricSpace Y := metrizableSpaceMetric Y
  ⟨⟨hf.comapMetricSpace f, rfl⟩⟩

@[deprecated (since := "2024-10-26")]
alias _root_.Embedding.metrizableSpace := IsEmbedding.metrizableSpace

instance MetrizableSpace.subtype [MetrizableSpace X] (s : Set X) : MetrizableSpace s :=
  IsEmbedding.subtypeVal.metrizableSpace

instance metrizableSpace_pi [∀ i, MetrizableSpace (π i)] : MetrizableSpace (∀ i, π i) := by
  cases nonempty_fintype ι
  letI := fun i => metrizableSpaceMetric (π i)
  infer_instance

theorem IsSeparable.secondCountableTopology [PseudoMetrizableSpace X] {s : Set X}
    (hs : IsSeparable s) : SecondCountableTopology s := by
  letI := pseudoMetrizableSpacePseudoMetric X
  have := hs.separableSpace
  exact UniformSpace.secondCountable_of_separable s

instance (X : Type*) [TopologicalSpace X] [c : CompactSpace X] [MetrizableSpace X] :
    SecondCountableTopology X := by
  obtain ⟨_, h⟩ := MetrizableSpace.exists_metric (X := X)
  rw [← h] at c ⊢
  infer_instance

end TopologicalSpace
