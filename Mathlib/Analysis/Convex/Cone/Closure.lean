/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid.Defs

/-!
# Closure of cones

We define the closures of pointed cones. This construction is primarily needed for
defining maps between proper cones. The current API is basic and should be extended as necessary.

-/

@[expose] public section

namespace PointedCone

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [Module 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/-- The closure of a pointed cone inside a topological space as a pointed cone. This
construction is mainly used for defining maps between proper cones. -/
protected def closure (K : PointedCone 𝕜 E) : PointedCone 𝕜 E where
  carrier := closure ↑K
  zero_mem' := subset_closure (zero_mem K)
  smul_mem' c _ h₁ := map_mem_closure (continuous_const_smul c.1) h₁ fun _ h₂ ↦ K.smul_mem c.2 h₂
  add_mem' h₁ h₂ := map_mem_closure₂ continuous_add h₁ h₂ (fun _ ha _ hb ↦ K.add_mem ha hb)

@[simp, norm_cast]
theorem coe_closure (K : PointedCone 𝕜 E) : (K.closure : Set E) = closure K :=
  rfl

@[simp]
protected theorem mem_closure {K : PointedCone 𝕜 E} {a : E} :
    a ∈ K.closure ↔ a ∈ closure (K : Set E) :=
  Iff.rfl

@[simp]
theorem closure_eq {K L : PointedCone 𝕜 E} : K.closure = L ↔ closure (K : Set E) = L :=
  SetLike.ext'_iff

end PointedCone
