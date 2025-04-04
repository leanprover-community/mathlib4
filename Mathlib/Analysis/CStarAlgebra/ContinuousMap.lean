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

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra (α →ᵇ A) where
  norm_mul_self_le := CStarRing.norm_mul_self_le

instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra (α →ᵇ A) where
  mul_comm := mul_comm

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
instance [CStarAlgebra A] : CStarAlgebra (α →ᵇ A) where
  norm_mul_self_le := CStarRing.norm_mul_self_le

instance [CommCStarAlgebra A] : CommCStarAlgebra (α →ᵇ A) where
  mul_comm := mul_comm

end BoundedContinuousFunction

namespace ContinuousMap

variable [TopologicalSpace α] [CompactSpace α]

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
instance [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C(α, A) where
  norm_mul_self_le := CStarRing.norm_mul_self_le

instance [NonUnitalCommCStarAlgebra A] : NonUnitalCommCStarAlgebra C(α, A) where
  mul_comm := mul_comm

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
instance [CStarAlgebra A] : CStarAlgebra C(α, A) where
  norm_mul_self_le := CStarRing.norm_mul_self_le

instance [CommCStarAlgebra A] : CommCStarAlgebra C(α, A) where
  mul_comm := mul_comm

end ContinuousMap

namespace ZeroAtInftyContinuousMap

open ZeroAtInfty

#adaptation_note /-- 2025-03-29 for lean4#7717 had to add `norm_mul_self_le` field. -/
instance [TopologicalSpace α] [NonUnitalCStarAlgebra A] : NonUnitalCStarAlgebra C₀(α, A) where
  norm_mul_self_le := CStarRing.norm_mul_self_le

instance [TopologicalSpace α] [NonUnitalCommCStarAlgebra A] :
    NonUnitalCommCStarAlgebra C₀(α, A) where
  mul_comm := mul_comm

end ZeroAtInftyContinuousMap
