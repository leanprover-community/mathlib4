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

namespace OrderIso
variable {G₀} [GroupWithZero G₀] [PartialOrder G₀]

section left
variable [PosMulMono G₀] [PosMulReflectLE G₀]

/-- `Equiv.mulLeft₀` as an order isomorphism. -/
@[simps! (config := { simpRhs := true })]
def mulLeft₀ (a : G₀) (ha : 0 < a) : G₀ ≃o G₀ where
  toEquiv := .mulLeft₀ a ha.ne'
  map_rel_iff' := mul_le_mul_left ha

variable [ZeroLEOneClass G₀]

lemma mulLeft₀_symm (a : G₀) (ha : 0 < a) : (mulLeft₀ a ha).symm = mulLeft₀ a⁻¹ (inv_pos.2 ha) := by
  ext; rfl

end left

section right
variable [MulPosMono G₀] [MulPosReflectLE G₀]

/-- `Equiv.mulRight₀` as an order isomorphism. -/
@[simps! (config := { simpRhs := true })]
def mulRight₀ (a : G₀) (ha : 0 < a) : G₀ ≃o G₀ where
  toEquiv := .mulRight₀ a ha.ne'
  map_rel_iff' := mul_le_mul_right ha

variable [ZeroLEOneClass G₀] [PosMulReflectLT G₀]

lemma mulRight₀_symm (a : G₀) (ha : 0 < a) :
    (mulRight₀ a ha).symm = mulRight₀ a⁻¹ (inv_pos.2 ha) := by ext; rfl

end right

/-- `Equiv.divRight₀` as an order isomorphism. -/
@[simps! (config := { simpRhs := true })]
def divRight₀ [ZeroLEOneClass G₀] [MulPosStrictMono G₀] [MulPosReflectLE G₀] [PosMulReflectLT G₀]
    (a : G₀) (ha : 0 < a) : G₀ ≃o G₀ where
  toEquiv := .divRight₀ a ha.ne'
  map_rel_iff' {b c} := by
    simp only [Equiv.divRight₀_apply, div_eq_mul_inv]
    exact mul_le_mul_right (a := a⁻¹) (inv_pos.mpr ha)

end OrderIso
