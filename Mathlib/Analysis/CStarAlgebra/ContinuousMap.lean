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

instance [NonUnitalRing A] [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra (α →ᵇ A) where

instance [Ring A] [CStarAlgebra A] : CStarAlgebra (α →ᵇ A) where

end BoundedContinuousFunction

namespace ContinuousMap

variable [TopologicalSpace α] [CompactSpace α]

instance [NonUnitalRing A] [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C(α, A) where

instance [Ring A] [CStarAlgebra A] : CStarAlgebra C(α, A) where

end ContinuousMap

namespace ZeroAtInftyContinuousMap

open ZeroAtInfty

instance [TopologicalSpace α] [NonUnitalRing A] [NonUnitalCStarAlgebra A] :
    NonUnitalCStarAlgebra C₀(α, A) where

end ZeroAtInftyContinuousMap
