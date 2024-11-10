/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Order.GroupWithZero.Unbundled
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Order.Hom.Basic

/-!
# Multiplication by a positive element as an order isomorphism
-/

variable {G₀} [GroupWithZero G₀] [Preorder G₀] [ZeroLEOneClass G₀] {a : G₀}

/-- `Equiv.mulLeft₀` as an order isomorphism. -/
@[simps! (config := { simpRhs := true })]
def OrderIso.mulLeft₀ [PosMulMono G₀] [PosMulReflectLE G₀] (a : G₀) (ha : 0 < a) : G₀ ≃o G₀ where
  toEquiv := .mulLeft₀ a ha.ne'
  map_rel_iff' := mul_le_mul_left ha

/-- `Equiv.mulRight₀` as an order isomorphism. -/
@[simps! (config := { simpRhs := true })]
def OrderIso.mulRight₀ [MulPosMono G₀] [MulPosReflectLE G₀] (a : G₀) (ha : 0 < a) : G₀ ≃o G₀ where
  toEquiv := .mulRight₀ a ha.ne'
  map_rel_iff' := mul_le_mul_right ha
