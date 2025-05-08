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

This files transfers ordered (semi)ring instances from `R` to `Rᵐᵒᵖ` and `Rᵃᵒᵖ`.
-/

variable {R : Type*}

namespace MulOpposite

instance [Semiring R] [PartialOrder R] [IsOrderedRing R] : IsOrderedRing Rᵐᵒᵖ where
  zero_le_one := zero_le_one (α := R)
  mul_le_mul_of_nonneg_left _ _ _ := mul_le_mul_of_nonneg_right (α := R)
  mul_le_mul_of_nonneg_right _ _ _ := mul_le_mul_of_nonneg_left (α := R)

end MulOpposite

namespace AddOpposite

instance [Semiring R] [PartialOrder R] [IsOrderedRing R] : IsOrderedRing Rᵃᵒᵖ where
  zero_le_one := zero_le_one (α := R)
  mul_le_mul_of_nonneg_left _ _ _ := mul_le_mul_of_nonneg_left (α := R)
  mul_le_mul_of_nonneg_right _ _ _ := mul_le_mul_of_nonneg_right (α := R)

end AddOpposite
