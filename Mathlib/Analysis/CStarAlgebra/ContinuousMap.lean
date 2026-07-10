/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty

/-! # C⋆-algebras of continuous functions

We place these here because, for reasons related to the import hierarchy, they cannot be placed in
earlier files.
-/

public section

variable {α A : Type*}

namespace BoundedContinuousFunction

variable [TopologicalSpace α]

noncomputable instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra (α →ᵇ A) where

noncomputable instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra (α →ᵇ A) where

noncomputable instance [CStarAlgebra A] : CStarAlgebra (α →ᵇ A) where

noncomputable instance [CommCStarAlgebra A] : CommCStarAlgebra (α →ᵇ A) where

end BoundedContinuousFunction

namespace ContinuousMap

variable [TopologicalSpace α] [CompactSpace α]

noncomputable instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C(α, A) where

noncomputable instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra C(α, A) where

noncomputable instance [CStarAlgebra A] : CStarAlgebra C(α, A) where

noncomputable instance [CommCStarAlgebra A] : CommCStarAlgebra C(α, A) where

end ContinuousMap

namespace ZeroAtInftyContinuousMap

open ZeroAtInfty

noncomputable
instance [TopologicalSpace α] [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C₀(α, A) where

noncomputable instance [TopologicalSpace α] [NonUnitalCommCStarAlgebra A] :
    NonUnitalCommCStarAlgebra C₀(α, A) where

end ZeroAtInftyContinuousMap
