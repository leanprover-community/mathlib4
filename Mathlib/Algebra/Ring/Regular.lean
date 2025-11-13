/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.GroupWithZero.Regular
import Mathlib.Algebra.Ring.Defs

/-!
# Lemmas about regular elements in rings.
-/


variable {α : Type*}

/-- Left `Mul` by a `k : α` over `[Ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `NoZeroDivisors`. -/
theorem isLeftRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, k * x = 0 → x = 0) : IsLeftRegular k := by
  refine fun x y (h' : k * x = k * y) => sub_eq_zero.mp (h _ ?_)
  rw [mul_sub, sub_eq_zero, h']

/-- Right `Mul` by a `k : α` over `[Ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `NoZeroDivisors`. -/
theorem isRightRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, x * k = 0 → x = 0) : IsRightRegular k := by
  refine fun x y (h' : x * k = y * k) => sub_eq_zero.mp (h _ ?_)
  rw [sub_mul, sub_eq_zero, h']

theorem isRegular_of_ne_zero' [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} (hk : k ≠ 0) :
    IsRegular k :=
  ⟨isLeftRegular_of_non_zero_divisor k fun _ h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk,
    isRightRegular_of_non_zero_divisor k fun _ h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk⟩

theorem isRegular_iff_ne_zero' [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α]
    {k : α} : IsRegular k ↔ k ≠ 0 :=
  ⟨fun h => by
    rintro rfl
    exact not_not.mpr h.left not_isLeftRegular_zero, isRegular_of_ne_zero'⟩

/-- A ring with no zero divisors is a `CancelMonoidWithZero`.

Note this is not an instance as it forms a typeclass loop. -/
abbrev NoZeroDivisors.toCancelMonoidWithZero [Ring α] [NoZeroDivisors α] :
    CancelMonoidWithZero α where
  mul_left_cancel_of_ne_zero ha := (isRegular_of_ne_zero' ha).1
  mul_right_cancel_of_ne_zero hb := (isRegular_of_ne_zero' hb).2

/-- A commutative ring with no zero divisors is a `CancelCommMonoidWithZero`.

Note this is not an instance as it forms a typeclass loop. -/
abbrev NoZeroDivisors.toCancelCommMonoidWithZero [CommRing α] [NoZeroDivisors α] :
    CancelCommMonoidWithZero α :=
  { NoZeroDivisors.toCancelMonoidWithZero, ‹CommRing α› with }

section IsDomain

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelMonoidWithZero [Semiring α] [IsDomain α] :
    CancelMonoidWithZero α where

variable [CommSemiring α] [IsDomain α]

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelCommMonoidWithZero : CancelCommMonoidWithZero α :=
  { mul_left_cancel_of_ne_zero := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero }

end IsDomain
