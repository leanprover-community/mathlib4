/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# Paracompactness of pseudometrizable spaces

This file proves Stone's theorem that every pseudometrizable space is paracompact. As a
consequence, every metrizable space is a T4 space.
-/

public section

namespace TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

-- See note [lower instance priority]
/-- **Stone's theorem**: every pseudometrizable space is paracompact. -/
instance (priority := 100) PseudoMetrizableSpace.paracompactSpace
    [PseudoMetrizableSpace X] : ParacompactSpace X := by
  letI : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  exact Metric.instParacompactSpace

/-- Every metrizable space is a T4 space. -/
theorem MetrizableSpace.t4Space [MetrizableSpace X] : T4Space X := inferInstance

end TopologicalSpace
