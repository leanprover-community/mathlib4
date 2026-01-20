/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.GroupWithZero.Regular
public import Mathlib.Algebra.Ring.Defs

/-!
# Lemmas about regular elements in rings.
-/

@[expose] public section


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

/-- A ring with no zero divisors is a cancellative `MonoidWithZero`.

Note this is not an instance as it forms a typeclass loop. -/
lemma NoZeroDivisors.toIsCancelMulZero [NonUnitalNonAssocRing α] [NoZeroDivisors α] :
    IsCancelMulZero α where
  mul_left_cancel_of_ne_zero ha := (isRegular_of_ne_zero' ha).1
  mul_right_cancel_of_ne_zero hb := (isRegular_of_ne_zero' hb).2

namespace IsDedekindFiniteMonoid

variable [Ring α]

/-- A ring is Dedekind-finite if and only if every element has at most one right inverse. -/
theorem iff_eq_of_mul_left_eq_one :
    IsDedekindFiniteMonoid α ↔ ∀ x y z : α, x * y = 1 → x * z = 1 → y = z := by
  refine (isDedekindFiniteMonoid_iff _).trans ⟨fun h x y z hxy hxz ↦ ?_, fun h x y eq ↦ ?_⟩
  · simpa [← mul_assoc, h hxz] using congr_arg (z * ·) hxy
  have := h _ _ (1 - y * x + y) eq <| by
    rw [mul_add, mul_sub, ← mul_assoc, eq, mul_one, one_mul, sub_self, zero_add]
  rwa [right_eq_add, sub_eq_zero, eq_comm] at this

/-- A ring is Dedekind-finite if and only if every element has at most one left inverse. -/
theorem iff_eq_of_mul_right_eq_one :
    IsDedekindFiniteMonoid α ↔ ∀ x y z : α, x * z = 1 → y * z = 1 → x = y := by
  refine (isDedekindFiniteMonoid_iff _).trans ⟨fun h x y z hxz hyz ↦ ?_, fun h x y eq ↦ ?_⟩
  · simpa [mul_assoc, h hyz] using congr_arg (· * y) hxz
  have := h _ (1 - y * x + x) _ eq <| by
    rw [add_mul, sub_mul, mul_assoc, eq, one_mul, mul_one, sub_self, zero_add]
  rwa [right_eq_add, sub_eq_zero, eq_comm] at this

end IsDedekindFiniteMonoid
