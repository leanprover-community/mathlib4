/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Semicontinuous

/-!
# Barrelled spaces
-/

section GeneralField

class BarrelledSpace (𝕜 E : Type _) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E]
    [TopologicalSpace E] : Prop where
  continuous_of_lowerSemicontinuous : ∀ p : Seminorm 𝕜 E, LowerSemicontinuous p → Continuous p



variable {𝕜 E : Type _} [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E]
    [TopologicalSpace E]

end GeneralField
