/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.Opposite
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Opposite

/-!
# Ordered ring instances for `MulOpposite`/`AddOpposite`

This files transfers ordered (semi)ring instances from `α` to `αᵐᵒᵖ` and `αᵃᵒᵖ`.
-/

variable {α : Type*}

namespace MulOpposite

instance [Semiring α] [PartialOrder α] [IsOrderedRing α] : IsOrderedRing αᵐᵒᵖ where
  zero_le_one := zero_le_one (α := α)
  mul_le_mul_of_nonneg_left _ _ _ := mul_le_mul_of_nonneg_right (α := α)
  mul_le_mul_of_nonneg_right _ _ _ := mul_le_mul_of_nonneg_left (α := α)

end MulOpposite

namespace AddOpposite

instance [Semiring α] [PartialOrder α] [IsOrderedRing α] : IsOrderedRing αᵃᵒᵖ where
  zero_le_one := zero_le_one (α := α)
  mul_le_mul_of_nonneg_left _ _ _ := mul_le_mul_of_nonneg_left (α := α)
  mul_le_mul_of_nonneg_right _ _ _ := mul_le_mul_of_nonneg_right (α := α)

end AddOpposite
