/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.MetricSpace.Instances

/-!
# Instances for metrizable spaces

Instances for products and pi types for pseudo-metrizable and metrizable spaces.
-/

namespace TopologicalSpace

open Set Filter Metric

variable {ι X Y : Type*} {π : ι → Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
  [∀ i, TopologicalSpace (π i)]

instance pseudoMetrizableSpace_prod [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y] :
    PseudoMetrizableSpace (X × Y) :=
  letI : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  letI : PseudoMetricSpace Y := pseudoMetrizableSpacePseudoMetric Y
  inferInstance
#align topological_space.pseudo_metrizable_space_prod TopologicalSpace.pseudoMetrizableSpace_prod

instance pseudoMetrizableSpace_pi [∀ i, PseudoMetrizableSpace (π i)] :
    PseudoMetrizableSpace (∀ i, π i) := by
  cases nonempty_fintype ι
  letI := fun i => pseudoMetrizableSpacePseudoMetric (π i)
  infer_instance
#align topological_space.pseudo_metrizable_space_pi TopologicalSpace.pseudoMetrizableSpace_pi

instance metrizableSpace_prod [MetrizableSpace X] [MetrizableSpace Y] : MetrizableSpace (X × Y) :=
  letI : MetricSpace X := metrizableSpaceMetric X
  letI : MetricSpace Y := metrizableSpaceMetric Y
  inferInstance
#align topological_space.metrizable_space_prod TopologicalSpace.metrizableSpace_prod

instance metrizableSpace_pi [∀ i, MetrizableSpace (π i)] : MetrizableSpace (∀ i, π i) := by
  cases nonempty_fintype ι
  letI := fun i => metrizableSpaceMetric (π i)
  infer_instance
#align topological_space.metrizable_space_pi TopologicalSpace.metrizableSpace_pi
