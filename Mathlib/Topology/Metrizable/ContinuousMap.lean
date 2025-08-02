/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Metrizability of `C(X, Y)`

If `X` is a weakly locally compact σ-compact space and `Y` is a (pseudo)metrizable space,
then `C(X, Y)` is a (pseudo)metrizable space.
-/

open TopologicalSpace

namespace ContinuousMap

variable {X Y : Type*}
  [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
  [TopologicalSpace Y]

instance [PseudoMetrizableSpace Y] : PseudoMetrizableSpace C(X, Y) :=
  let _ := pseudoMetrizableSpacePseudoMetric Y
  inferInstance

instance [MetrizableSpace Y] : MetrizableSpace C(X, Y) :=
  let _ := metrizableSpaceMetric Y
  UniformSpace.metrizableSpace

end ContinuousMap
