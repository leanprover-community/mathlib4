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

instance [OrderedSemiring α] : OrderedSemiring αᵐᵒᵖ where
  __ := instSemiring
  __ := instOrderedAddCommMonoid
  zero_le_one := zero_le_one (α := α)
  mul_le_mul_of_nonneg_left _ _ _ := mul_le_mul_of_nonneg_right (α := α)
  mul_le_mul_of_nonneg_right _ _ _ := mul_le_mul_of_nonneg_left (α := α)

instance [OrderedRing α] : OrderedRing αᵐᵒᵖ where
  __ := instRing
  __ := instOrderedAddCommGroup
  __ := instOrderedSemiring
  mul_nonneg _a _b ha hb := mul_nonneg (α := α) hb ha

end MulOpposite

namespace AddOpposite

instance [OrderedSemiring α] : OrderedSemiring αᵃᵒᵖ where
  __ := instSemiring
  __ := instOrderedAddCommMonoid
  zero_le_one := zero_le_one (α := α)
  mul_le_mul_of_nonneg_left _ _ _ := mul_le_mul_of_nonneg_left (α := α)
  mul_le_mul_of_nonneg_right _ _ _ := mul_le_mul_of_nonneg_right (α := α)

instance [OrderedRing α] : OrderedRing αᵐᵒᵖ where
  __ := instRing
  __ := instOrderedAddCommGroup
  __ := instOrderedSemiring
  mul_nonneg _a _b := mul_nonneg (α := α)

end AddOpposite
