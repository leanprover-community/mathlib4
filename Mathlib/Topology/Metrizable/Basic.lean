/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.MetricSpace.Basic

#align_import topology.metric_space.metrizable from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Metrizability of a T₃ topological space with second countable topology

In this file we define metrizable topological spaces, i.e., topological spaces for which there
exists a metric space structure that generates the same topology.
-/


open Set Filter Metric
open scoped Filter Topology

namespace TopologicalSpace

variable {ι X Y : Type*} {π : ι → Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
  [∀ i, TopologicalSpace (π i)]

/-- A topological space is *pseudo metrizable* if there exists a pseudo metric space structure
compatible with the topology. To endow such a space with a compatible distance, use
`letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X`. -/
class PseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_pseudo_metric : ∃ m : PseudoMetricSpace X, m.toUniformSpace.toTopologicalSpace = t
#align topological_space.pseudo_metrizable_space TopologicalSpace.PseudoMetrizableSpace

instance (priority := 100) _root_.PseudoMetricSpace.toPseudoMetrizableSpace {X : Type*}
    [m : PseudoMetricSpace X] : PseudoMetrizableSpace X :=
  ⟨⟨m, rfl⟩⟩
#align pseudo_metric_space.to_pseudo_metrizable_space PseudoMetricSpace.toPseudoMetrizableSpace

/-- Construct on a metrizable space a metric compatible with the topology. -/
noncomputable def pseudoMetrizableSpacePseudoMetric (X : Type*) [TopologicalSpace X]
    [h : PseudoMetrizableSpace X] : PseudoMetricSpace X :=
  h.exists_pseudo_metric.choose.replaceTopology h.exists_pseudo_metric.choose_spec.symm
#align topological_space.pseudo_metrizable_space_pseudo_metric TopologicalSpace.pseudoMetrizableSpacePseudoMetric

instance pseudoMetrizableSpace_prod [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y] :
    PseudoMetrizableSpace (X × Y) :=
  letI : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  letI : PseudoMetricSpace Y := pseudoMetrizableSpacePseudoMetric Y
  inferInstance
#align topological_space.pseudo_metrizable_space_prod TopologicalSpace.pseudoMetrizableSpace_prod

/-- Given an inducing map of a topological space into a pseudo metrizable space, the source space
is also pseudo metrizable. -/
theorem _root_.Inducing.pseudoMetrizableSpace [PseudoMetrizableSpace Y] {f : X → Y}
    (hf : Inducing f) : PseudoMetrizableSpace X :=
  letI : PseudoMetricSpace Y := pseudoMetrizableSpacePseudoMetric Y
  ⟨⟨hf.comapPseudoMetricSpace, rfl⟩⟩
#align inducing.pseudo_metrizable_space Inducing.pseudoMetrizableSpace

/-- Every pseudo-metrizable space is first countable. -/
instance (priority := 100) PseudoMetrizableSpace.firstCountableTopology
    [h : PseudoMetrizableSpace X] : FirstCountableTopology X := by
  rcases h with ⟨_, hm⟩
  rw [← hm]
  exact @UniformSpace.firstCountableTopology X PseudoMetricSpace.toUniformSpace
    EMetric.instIsCountablyGeneratedUniformity
#align topological_space.pseudo_metrizable_space.first_countable_topology TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology

instance PseudoMetrizableSpace.subtype [PseudoMetrizableSpace X] (s : Set X) :
    PseudoMetrizableSpace s :=
  inducing_subtype_val.pseudoMetrizableSpace
#align topological_space.pseudo_metrizable_space.subtype TopologicalSpace.PseudoMetrizableSpace.subtype

instance pseudoMetrizableSpace_pi [∀ i, PseudoMetrizableSpace (π i)] :
    PseudoMetrizableSpace (∀ i, π i) := by
  cases nonempty_fintype ι
  letI := fun i => pseudoMetrizableSpacePseudoMetric (π i)
  infer_instance
#align topological_space.pseudo_metrizable_space_pi TopologicalSpace.pseudoMetrizableSpace_pi

/-- A topological space is metrizable if there exists a metric space structure compatible with the
topology. To endow such a space with a compatible distance, use
`letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X`. -/
class MetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_metric : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t
#align topological_space.metrizable_space TopologicalSpace.MetrizableSpace

instance (priority := 100) _root_.MetricSpace.toMetrizableSpace {X : Type*} [m : MetricSpace X] :
    MetrizableSpace X :=
  ⟨⟨m, rfl⟩⟩
#align metric_space.to_metrizable_space MetricSpace.toMetrizableSpace

instance (priority := 100) MetrizableSpace.toPseudoMetrizableSpace [h : MetrizableSpace X] :
    PseudoMetrizableSpace X :=
  let ⟨m, hm⟩ := h.1
  ⟨⟨m.toPseudoMetricSpace, hm⟩⟩
#align topological_space.metrizable_space.to_pseudo_metrizable_space TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace

/-- Construct on a metrizable space a metric compatible with the topology. -/
noncomputable def metrizableSpaceMetric (X : Type*) [TopologicalSpace X] [h : MetrizableSpace X] :
    MetricSpace X :=
  h.exists_metric.choose.replaceTopology h.exists_metric.choose_spec.symm
#align topological_space.metrizable_space_metric TopologicalSpace.metrizableSpaceMetric

instance (priority := 100) t2Space_of_metrizableSpace [MetrizableSpace X] : T2Space X :=
  letI : MetricSpace X := metrizableSpaceMetric X
  inferInstance
#align topological_space.t2_space_of_metrizable_space TopologicalSpace.t2Space_of_metrizableSpace

instance metrizableSpace_prod [MetrizableSpace X] [MetrizableSpace Y] : MetrizableSpace (X × Y) :=
  letI : MetricSpace X := metrizableSpaceMetric X
  letI : MetricSpace Y := metrizableSpaceMetric Y
  inferInstance
#align topological_space.metrizable_space_prod TopologicalSpace.metrizableSpace_prod

/-- Given an embedding of a topological space into a metrizable space, the source space is also
metrizable. -/
theorem _root_.Embedding.metrizableSpace [MetrizableSpace Y] {f : X → Y} (hf : Embedding f) :
    MetrizableSpace X :=
  letI : MetricSpace Y := metrizableSpaceMetric Y
  ⟨⟨hf.comapMetricSpace f, rfl⟩⟩
#align embedding.metrizable_space Embedding.metrizableSpace

instance MetrizableSpace.subtype [MetrizableSpace X] (s : Set X) : MetrizableSpace s :=
  embedding_subtype_val.metrizableSpace
#align topological_space.metrizable_space.subtype TopologicalSpace.MetrizableSpace.subtype

instance metrizableSpace_pi [∀ i, MetrizableSpace (π i)] : MetrizableSpace (∀ i, π i) := by
  cases nonempty_fintype ι
  letI := fun i => metrizableSpaceMetric (π i)
  infer_instance
#align topological_space.metrizable_space_pi TopologicalSpace.metrizableSpace_pi

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
