/-
Copyright (c) 2023 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
module

public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Closure
import Mathlib.Topology.Continuous

/-!
# Closure of cones

We define the closures of convex and pointed cones. This construction is primarily needed for
defining maps between proper cones. The current API is basic and should be extended as necessary.

-/

@[expose] public section

namespace ConvexCone

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [SMul 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

/-- The closure of a convex cone inside a topological space as a convex cone. This
construction is mainly used for defining maps between proper cones. -/
protected def closure (K : ConvexCone 𝕜 E) : ConvexCone 𝕜 E where
  carrier := closure ↑K
  smul_mem' c hc _ h₁ := map_mem_closure (by fun_prop) h₁ fun _ h₂ ↦ K.smul_mem hc h₂
  add_mem' _ h₁ _ h₂ := map_mem_closure₂ continuous_add h₁ h₂ K.add_mem

@[simp, norm_cast]
theorem coe_closure (K : ConvexCone 𝕜 E) : (K.closure : Set E) = closure K :=
  rfl

@[simp]
protected theorem mem_closure {K : ConvexCone 𝕜 E} {a : E} :
    a ∈ K.closure ↔ a ∈ closure (K : Set E) :=
  Iff.rfl

@[simp]
theorem closure_eq {K L : ConvexCone 𝕜 E} : K.closure = L ↔ closure (K : Set E) = L :=
  SetLike.ext'_iff

end ConvexCone



namespace PointedCone

variable {𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E] [Module 𝕜 E]
  [ContinuousConstSMul 𝕜 E]

lemma toConvexCone_closure_pointed (K : PointedCone 𝕜 E) : (K : ConvexCone 𝕜 E).closure.Pointed :=
  subset_closure <| PointedCone.pointed_toConvexCone _

/-- The closure of a pointed cone inside a topological space as a pointed cone. This
construction is mainly used for defining maps between proper cones. -/
protected def closure (K : PointedCone 𝕜 E) : PointedCone 𝕜 E :=
  K.toConvexCone.closure.toPointedCone K.toConvexCone_closure_pointed

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
