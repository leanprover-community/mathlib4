/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Convex.ContinuousLinearEquiv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# (Strict) convexity and linear isometries

In this file we prove some basic lemmas about (strict) convexity and linear isometries.
-/

@[expose] public section

open Function Set Metric
open scoped Convex

section SeminormedAddCommGroup

variable {𝕜 E F : Type*}
  [NormedField 𝕜] [PartialOrder 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

@[simp]
lemma LinearIsometryEquiv.strictConvex_preimage {s : Set F} (e : E ≃ₗᵢ[𝕜] F) :
    StrictConvex 𝕜 (e ⁻¹' s) ↔ StrictConvex 𝕜 s :=
  e.toContinuousLinearEquiv.strictConvex_preimage

@[simp]
lemma LinearIsometryEquiv.strictConvex_image {s : Set E} (e : E ≃ₗᵢ[𝕜] F) :
    StrictConvex 𝕜 (e '' s) ↔ StrictConvex 𝕜 s :=
  e.toContinuousLinearEquiv.strictConvex_image

end SeminormedAddCommGroup

variable {𝕜 E F : Type*} [NormedField 𝕜] [PartialOrder 𝕜]

lemma StrictConvex.linearIsometry_preimage [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set F}
    (hs : StrictConvex 𝕜 s) (e : E →ₗᵢ[𝕜] F) : StrictConvex 𝕜 (e ⁻¹' s) :=
  hs.linear_preimage _ e.continuous e.injective

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

protected lemma LinearIsometryEquiv.strictConvexSpace_iff (e : E ≃ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 E ↔ StrictConvexSpace 𝕜 F := by
  simp only [strictConvexSpace_iff, ← map_zero e, ← e.image_closedBall, e.strictConvex_image]

lemma LinearIsometry.strictConvexSpace_range_iff (e : E →ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 (e : E →ₗ[𝕜] F).range ↔ StrictConvexSpace 𝕜 E :=
  e.equivRange.strictConvexSpace_iff.symm

instance LinearIsometry.strictConvexSpace_range [StrictConvexSpace 𝕜 E] (e : E →ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 (e : E →ₗ[𝕜] F).range :=
  e.strictConvexSpace_range_iff.mpr ‹_›

lemma LinearIsometry.strictConvexSpace [StrictConvexSpace 𝕜 F] (f : E →ₗᵢ[𝕜] F) :
    StrictConvexSpace 𝕜 E where
  strictConvex_closedBall r hr := by
    rw [← f.isometry.preimage_closedBall]
    exact (strictConvex_closedBall _ _ _).linearIsometry_preimage _

/-- A vector subspace of a strict convex space is a strict convex space.

This instance has priority 900
to make sure that instances like `LinearIsometry.strictConvexSpace_range`
are tried before this one. -/
instance (priority := 900) Submodule.instStrictConvexSpace [StrictConvexSpace 𝕜 E]
    (p : Submodule 𝕜 E) : StrictConvexSpace 𝕜 p :=
  p.subtypeₗᵢ.strictConvexSpace
