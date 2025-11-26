/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.Group.Submonoid.Defs

/-!
# Submagmas with zero inherit cancellations
-/

namespace MulZeroMemClass

variable {M₀ : Type*} [Mul M₀] [Zero M₀] {S : Type*} [SetLike S M₀] [MulMemClass S M₀]
  [ZeroMemClass S M₀] (s : S)

/-- A submagma with zero of a left cancellative magma with zero inherits left cancellation. -/
instance isLeftCancelMulZero [IsLeftCancelMulZero M₀] : IsLeftCancelMulZero s :=
  Subtype.coe_injective.isLeftCancelMulZero Subtype.val rfl fun _ _ => rfl

/-- A submagma with zero of a right cancellative magma with zero inherits right cancellation. -/
instance isRightCancelMulZero [IsRightCancelMulZero M₀] : IsRightCancelMulZero s :=
  Subtype.coe_injective.isRightCancelMulZero Subtype.val rfl fun _ _ => rfl

/-- A submagma with zero of a cancellative magma with zero inherits cancellation. -/
instance isCancelMulZero [IsCancelMulZero M₀] : IsCancelMulZero s where

end MulZeroMemClass
