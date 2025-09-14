/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-! # C⋆-algebras of continuous functions

We place these here because, for reasons related to the import hierarchy, they cannot be placed in
earlier files.
-/

variable {α A : Type*}
noncomputable section

namespace BoundedContinuousFunction

variable [TopologicalSpace α]

example [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra (α →ᵇ A) := by infer_instance

example [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra (α →ᵇ A) := by infer_instance

example [CStarAlgebra A] : CStarAlgebra (α →ᵇ A) := by infer_instance

example [CommCStarAlgebra A] : CommCStarAlgebra (α →ᵇ A) := by infer_instance

end BoundedContinuousFunction

namespace ContinuousMap

variable [TopologicalSpace α] [CompactSpace α]

example [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C(α, A) := by infer_instance

example [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra C(α, A) := by infer_instance

example [CStarAlgebra A] : CStarAlgebra C(α, A) := by infer_instance

example [CommCStarAlgebra A] : CommCStarAlgebra C(α, A) := by infer_instance

end ContinuousMap

namespace ZeroAtInftyContinuousMap

open ZeroAtInfty

example [TopologicalSpace α] [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C₀(α, A) where

example [TopologicalSpace α] [NonUnitalCommCStarAlgebra A] :
    NonUnitalCommCStarAlgebra C₀(α, A) := by infer_instance

end ZeroAtInftyContinuousMap
