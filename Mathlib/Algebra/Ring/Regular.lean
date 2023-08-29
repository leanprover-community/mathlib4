/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Regular.Basic
import Mathlib.Algebra.Ring.Defs

#align_import algebra.ring.regular from "leanprover-community/mathlib"@"2f3994e1b117b1e1da49bcfb67334f33460c3ce4"

/-!
# Lemmas about regular elements in rings.
-/


variable {α : Type*}

/-- Left `Mul` by a `k : α` over `[Ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `NoZeroDivisors`. -/
theorem isLeftRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, k * x = 0 → x = 0) : IsLeftRegular k := by
  refine' fun x y (h' : k * x = k * y) => sub_eq_zero.mp (h _ _)
  -- ⊢ k * (x - y) = 0
  rw [mul_sub, sub_eq_zero, h']
  -- 🎉 no goals
#align is_left_regular_of_non_zero_divisor isLeftRegular_of_non_zero_divisor

/-- Right `Mul` by a `k : α` over `[Ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `NoZeroDivisors`. -/
theorem isRightRegular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α)
    (h : ∀ x : α, x * k = 0 → x = 0) : IsRightRegular k := by
  refine' fun x y (h' : x * k = y * k) => sub_eq_zero.mp (h _ _)
  -- ⊢ (x - y) * k = 0
  rw [sub_mul, sub_eq_zero, h']
  -- 🎉 no goals
#align is_right_regular_of_non_zero_divisor isRightRegular_of_non_zero_divisor

theorem isRegular_of_ne_zero' [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} (hk : k ≠ 0) :
    IsRegular k :=
  ⟨isLeftRegular_of_non_zero_divisor k fun _ h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk,
    isRightRegular_of_non_zero_divisor k fun _ h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk⟩
#align is_regular_of_ne_zero' isRegular_of_ne_zero'

theorem isRegular_iff_ne_zero' [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α]
    {k : α} : IsRegular k ↔ k ≠ 0 :=
  ⟨fun h => by
    rintro rfl
    -- ⊢ False
    exact not_not.mpr h.left not_isLeftRegular_zero, isRegular_of_ne_zero'⟩
    -- 🎉 no goals
#align is_regular_iff_ne_zero' isRegular_iff_ne_zero'

/-- A ring with no zero divisors is a `CancelMonoidWithZero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def NoZeroDivisors.toCancelMonoidWithZero [Ring α] [NoZeroDivisors α] : CancelMonoidWithZero α :=
  { (by infer_instance : MonoidWithZero α) with
        -- 🎉 no goals
    mul_left_cancel_of_ne_zero := fun ha =>
      @IsRegular.left _ _ _ (isRegular_of_ne_zero' ha) _ _,
    mul_right_cancel_of_ne_zero := fun hb =>
      @IsRegular.right _ _ _ (isRegular_of_ne_zero' hb) _ _ }
#align no_zero_divisors.to_cancel_monoid_with_zero NoZeroDivisors.toCancelMonoidWithZero

/-- A commutative ring with no zero divisors is a `CancelCommMonoidWithZero`.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def NoZeroDivisors.toCancelCommMonoidWithZero [CommRing α] [NoZeroDivisors α] :
    CancelCommMonoidWithZero α :=
  { NoZeroDivisors.toCancelMonoidWithZero, ‹CommRing α› with }
#align no_zero_divisors.to_cancel_comm_monoid_with_zero NoZeroDivisors.toCancelCommMonoidWithZero

section IsDomain

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelMonoidWithZero [Semiring α] [IsDomain α] :
    CancelMonoidWithZero α :=
  { }
#align is_domain.to_cancel_monoid_with_zero IsDomain.toCancelMonoidWithZero

variable [CommSemiring α] [IsDomain α]

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelCommMonoidWithZero : CancelCommMonoidWithZero α :=
  { mul_left_cancel_of_ne_zero := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero }
#align is_domain.to_cancel_comm_monoid_with_zero IsDomain.toCancelCommMonoidWithZero

end IsDomain
