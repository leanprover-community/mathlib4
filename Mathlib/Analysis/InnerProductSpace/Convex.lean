/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

/-!
# Convexity properties of inner product spaces

## Main results

- `InnerProductSpace.toUniformConvexSpace`: an inner product space is a uniformly convex space.

## Tags

inner product space, Hilbert space, norm

-/

@[expose] public section


noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp
open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [SeminormedAddCommGroup F] [InnerProductSpace ℝ F]

-- See note [lower instance priority]
instance (priority := 100) InnerProductSpace.toUniformConvexSpace : UniformConvexSpace F :=
  ⟨fun ε hε => by
    refine
      ⟨2 - √(4 - ε ^ 2), sub_pos_of_lt <| (sqrt_lt' zero_lt_two).2 ?_, fun x hx y hy hxy => ?_⟩
    · norm_num
      exact pow_pos hε _
    rw [sub_sub_cancel]
    refine le_sqrt_of_sq_le ?_
    rw [sq, eq_sub_iff_add_eq.2 (parallelogram_law_with_norm_mul ℝ x y), ← sq ‖x - y‖, hx, hy]
    ring_nf
    gcongr⟩
