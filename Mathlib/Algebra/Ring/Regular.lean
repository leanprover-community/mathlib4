/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# Lemmas about regular elements in rings.
-/


variable {α : Type _}

/-- Left `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
theorem is_left_regular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, k * x = 0 → x = 0) : IsLeftRegular k := by
  refine' fun x y (h' : k * x = k * y) => sub_eq_zero.mp (h _ _)
  rw [mul_sub, sub_eq_zero, h']
#align is_left_regular_of_non_zero_divisor is_left_regular_of_non_zero_divisor

/-- Right `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
theorem is_right_regular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, x * k = 0 → x = 0) : IsRightRegular k := by
  refine' fun x y (h' : x * k = y * k) => sub_eq_zero.mp (h _ _)
  rw [sub_mul, sub_eq_zero, h']
#align is_right_regular_of_non_zero_divisor is_right_regular_of_non_zero_divisor

theorem is_regular_of_ne_zero' [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} (hk : k ≠ 0) :
    IsRegular k :=
  ⟨is_left_regular_of_non_zero_divisor k fun x h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk,
    is_right_regular_of_non_zero_divisor k fun x h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk⟩
#align is_regular_of_ne_zero' is_regular_of_ne_zero'

theorem is_regular_iff_ne_zero' [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α]
    {k : α} : IsRegular k ↔ k ≠ 0 :=
  ⟨fun h => by
    rintro rfl
    exact not_not.mpr h.left not_is_left_regular_zero, is_regular_of_ne_zero'⟩
#align is_regular_iff_ne_zero' is_regular_iff_ne_zero'

/-- A ring with no zero divisors is a `cancel_monoid_with_zero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def NoZeroDivisors.toCancelMonoidWithZero [Ring α] [NoZeroDivisors α] : CancelMonoidWithZero α :=
  { (by infer_instance : MonoidWithZero α) with
    mul_left_cancel_of_ne_zero := fun a b c ha =>
      @IsRegular.left _ _ _ (is_regular_of_ne_zero' ha) _ _,
    mul_right_cancel_of_ne_zero := fun a b c hb =>
      @IsRegular.right _ _ _ (is_regular_of_ne_zero' hb) _ _ }
#align no_zero_divisors.to_cancel_monoid_with_zero NoZeroDivisors.toCancelMonoidWithZero

/-- A commutative ring with no zero divisors is a `cancel_comm_monoid_with_zero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def NoZeroDivisors.toCancelCommMonoidWithZero [CommRing α] [NoZeroDivisors α] :
    CancelCommMonoidWithZero α :=
  { NoZeroDivisors.toCancelMonoidWithZero, (by infer_instance : CommMonoidWithZero α) with }
#align no_zero_divisors.to_cancel_comm_monoid_with_zero NoZeroDivisors.toCancelCommMonoidWithZero

section IsDomain

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelMonoidWithZero [Ring α] [IsDomain α] :
    CancelMonoidWithZero α :=
  NoZeroDivisors.toCancelMonoidWithZero
#align is_domain.to_cancel_monoid_with_zero IsDomain.toCancelMonoidWithZero

variable [CommRing α] [IsDomain α]

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelCommMonoidWithZero : CancelCommMonoidWithZero α :=
  NoZeroDivisors.toCancelCommMonoidWithZero
#align is_domain.to_cancel_comm_monoid_with_zero IsDomain.toCancelCommMonoidWithZero

end IsDomain
