/-
Copyright (c) 2023 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/

import Mathlib.Topology.Metrizable.Basic

/-!
# Second-countability of pseudometrizable Lindelöf spaces

Factored out from `Mathlib/Topology/Compactness/Lindelof.lean`
to avoid circular dependencies.
-/

variable {X : Type*} [TopologicalSpace X]

open Set Filter Topology TopologicalSpace

instance SecondCountableTopology.ofPseudoMetrizableSpaceLindelofSpace [PseudoMetrizableSpace X]
    [LindelofSpace X] : SecondCountableTopology X :=
  inferInstance
