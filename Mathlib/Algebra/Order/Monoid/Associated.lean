/-
Copyright (c) 2022 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Order on associates

This file shows that divisibility makes associates into a canonically ordered monoid.
-/

@[expose] public section

variable {M : Type*} [CancelCommMonoidWithZero M]

namespace Associates

instance instIsOrderedMonoid : IsOrderedMonoid (Associates M) where
  mul_le_mul_left := by rintro a _ ⟨d, rfl⟩ c; exact ⟨d, mul_right_comm ..⟩

instance : CanonicallyOrderedMul (Associates M) where
  exists_mul_of_le h := h
  le_mul_self _ b := ⟨b, mul_comm ..⟩
  le_self_mul _ b := ⟨b, rfl⟩

end Associates
