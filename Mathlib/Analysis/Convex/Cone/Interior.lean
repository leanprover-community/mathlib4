/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Geometry.Convex.Cone.Basic
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Interior of convex cones

The interior of a convex cone is a convex cone. The coercion and membership API parallels
`ConvexCone.closure`.
-/

@[expose] public section

open Set
open scoped Pointwise

namespace ConvexCone

variable {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [ContinuousAdd E] [Module 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/-- The interior of a convex cone as a convex cone. -/
protected def interior (C : ConvexCone 𝕜 E) : ConvexCone 𝕜 E where
  carrier := interior (C : Set E)
  smul_mem' _c hc _ hx := interior_mono (smul_set_subset_iff.2 fun _ ↦ C.smul_mem hc)
    ((interior_smul₀ hc.ne' (C : Set E)).ge (smul_mem_smul_set hx))
  add_mem' _ hx _ hy := interior_mono (add_subset_iff.2 fun _ h _ h' ↦ C.add_mem h h')
    (subset_interior_add (add_mem_add hx hy))

@[simp, norm_cast]
theorem coe_interior (C : ConvexCone 𝕜 E) : (C.interior : Set E) = interior (C : Set E) :=
  rfl

@[simp]
protected theorem mem_interior {C : ConvexCone 𝕜 E} {a : E} :
    a ∈ C.interior ↔ a ∈ interior (C : Set E) :=
  Iff.rfl

@[simp]
theorem interior_eq {C D : ConvexCone 𝕜 E} : C.interior = D ↔ interior (C : Set E) = D :=
  SetLike.ext'_iff

end ConvexCone
