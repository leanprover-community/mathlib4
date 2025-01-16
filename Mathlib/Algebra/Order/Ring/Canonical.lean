/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Canonically ordered rings and semirings.
-/


open Function

universe u

variable {α : Type u}

set_option linter.deprecated false in
/-- A canonically ordered commutative semiring is an ordered, commutative semiring in which `a ≤ b`
iff there exists `c` with `b = a + c`. This is satisfied by the natural numbers, for example, but
not the integers or other ordered groups. -/
@[deprecated "Use `[OrderedCommSemiring α] [CanonicallyOrderedAdd α] [NoZeroDivisors α]` instead."
  (since := "2025-01-13")]
structure CanonicallyOrderedCommSemiring (α : Type*) extends CanonicallyOrderedAddCommMonoid α,
    CommSemiring α where
  /-- No zero divisors. -/
  protected eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : α}, a * b = 0 → a = 0 ∨ b = 0

attribute [nolint docBlame] CanonicallyOrderedCommSemiring.toCommSemiring

-- see Note [lower instance priority]
instance (priority := 10) CanonicallyOrderedAdd.toZeroLEOneClass
    [AddZeroClass α] [One α] [LE α] [CanonicallyOrderedAdd α] : ZeroLEOneClass α where
  zero_le_one := zero_le _

-- this holds more generally if we refactor `Odd` to use
-- either `2 • t` or `t + t` instead of `2 * t`.
lemma Odd.pos [Semiring α] [PartialOrder α] [CanonicallyOrderedAdd α] [Nontrivial α] {a : α} :
    Odd a → 0 < a := by
  rintro ⟨k, rfl⟩; simp

namespace CanonicallyOrderedAdd

-- see Note [lower instance priority]
instance (priority := 100) toMulLeftMono [NonUnitalNonAssocSemiring α]
    [LE α] [CanonicallyOrderedAdd α] : MulLeftMono α := by
  refine ⟨fun a b c h => ?_⟩; dsimp
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [mul_add]
  apply self_le_add_right

variable [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]

-- TODO: make it an instance
lemma toIsOrderedMonoid : IsOrderedMonoid α where
  mul_le_mul_left _ _ := mul_le_mul_left'

-- TODO: make it an instance
lemma toIsOrderedRing : IsOrderedRing α where
  zero_le_one := zero_le _
  add_le_add_left _ _ := add_le_add_left
  mul_le_mul_of_nonneg_left _ _ _ h _ := mul_le_mul_left' h _
  mul_le_mul_of_nonneg_right _ _ _ h _ := mul_le_mul_right' h _

-- See note [reducible non-instances]
/-- Construct an `OrderedCommMonoid` from a canonically ordered `CommSemiring`. -/
abbrev toOrderedCommMonoid : OrderedCommMonoid α where
  mul_le_mul_left _ _ := mul_le_mul_left'

-- See note [reducible non-instances]
/-- Construct an `OrderedCommSemiring` from a canonically ordered `CommSemiring`. -/
abbrev toOrderedCommSemiring : OrderedCommSemiring α where
  mul_comm := mul_comm
  zero_le_one := zero_le _
  add_le_add_left _ _ := add_le_add_left
  mul_le_mul_of_nonneg_left := fun _ _ _ h _ => mul_le_mul_left' h _
  mul_le_mul_of_nonneg_right := fun _ _ _ h _ => mul_le_mul_right' h _

@[simp]
protected theorem mul_pos [NoZeroDivisors α] {a b : α} :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]

lemma pow_pos [NoZeroDivisors α] {a : α} (ha : 0 < a) (n : ℕ) : 0 < a ^ n :=
  pos_iff_ne_zero.2 <| pow_ne_zero _ ha.ne'

protected lemma mul_lt_mul_of_lt_of_lt
    [PosMulStrictMono α] {a b c d : α} (hab : a < b) (hcd : c < d) :
    a * c < b * d := by
  -- TODO: This should be an instance but it currently times out
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  obtain rfl | hc := eq_zero_or_pos c
  · rw [mul_zero]
    exact mul_pos ((zero_le _).trans_lt hab) hcd
  · exact mul_lt_mul_of_pos' hab hcd hc ((zero_le _).trans_lt hab)

end CanonicallyOrderedAdd

section Sub

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)]

namespace AddLECancellable

protected theorem mul_tsub {a b c : α}
    (h : AddLECancellable (a * c)) : a * (b - c) = a * b - a * c := by
  obtain (hbc | hcb) := total_of (· ≤ ·) b c
  · rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_left' hbc a)]
  · apply h.eq_tsub_of_add_eq
    rw [← mul_add, tsub_add_cancel_of_le hcb]

protected theorem tsub_mul [MulRightMono α] {a b c : α}
    (h : AddLECancellable (b * c)) : (a - b) * c = a * c - b * c := by
  obtain (hab | hba) := total_of (· ≤ ·) a b
  · rw [tsub_eq_zero_iff_le.2 hab, zero_mul, tsub_eq_zero_iff_le.2 (mul_le_mul_right' hab c)]
  · apply h.eq_tsub_of_add_eq
    rw [← add_mul, tsub_add_cancel_of_le hba]

end AddLECancellable

variable [AddLeftReflectLE α]

theorem mul_tsub (a b c : α) : a * (b - c) = a * b - a * c :=
  Contravariant.AddLECancellable.mul_tsub

theorem tsub_mul [MulRightMono α] (a b c : α) :
    (a - b) * c = a * c - b * c :=
  Contravariant.AddLECancellable.tsub_mul

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)]

lemma mul_tsub_one [AddLeftReflectLE α] (a b : α) :
    a * (b - 1) = a * b - a := by rw [mul_tsub, mul_one]
lemma tsub_one_mul [MulRightMono α] [AddLeftReflectLE α] (a b : α) :
    (a - 1) * b = a * b - b := by rw [tsub_mul, one_mul]

end NonAssocSemiring

section CommSemiring

variable [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)] [AddLeftReflectLE α]

/-- The `tsub` version of `mul_self_sub_mul_self`. Notably, this holds for `Nat` and `NNReal`. -/
theorem mul_self_tsub_mul_self (a b : α) :
    a * a - b * b = (a + b) * (a - b) := by
  rw [mul_tsub, add_mul, add_mul, tsub_add_eq_tsub_tsub, mul_comm b a, add_tsub_cancel_right]

/-- The `tsub` version of `sq_sub_sq`. Notably, this holds for `Nat` and `NNReal`. -/
theorem sq_tsub_sq (a b : α) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq, mul_self_tsub_mul_self]

theorem mul_self_tsub_one (a : α) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← mul_self_tsub_mul_self, mul_one]

end CommSemiring

end Sub
