/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Sub.Canonical
import Mathlib.Algebra.Ring.Parity

#align_import algebra.order.ring.canonical from "leanprover-community/mathlib"@"824f9ae93a4f5174d2ea948e2d75843dd83447bb"

/-!
# Canonically ordered rings and semirings.

-/


open Function

universe u

variable {α : Type u} {β : Type*}

-- see Note [lower instance priority]
instance (priority := 10) CanonicallyOrderedAdd.toZeroLEOneClass
    [AddZeroClass α] [One α] [LE α] [CanonicallyOrderedAdd α] : ZeroLEOneClass α where
  zero_le_one := zero_le _

-- this holds more generally if we refactor `Odd` to use
-- either `2 • t` or `t + t` instead of `2 * t`.
lemma Odd.pos [Semiring α] [PartialOrder α] [CanonicallyOrderedAdd α] [Nontrivial α] {a : α} :
    Odd a → 0 < a := by
  rintro ⟨k, rfl⟩; simp
#align odd.pos Odd.pos

namespace CanonicallyOrderedAdd

-- see Note [lower instance priority]
instance (priority := 100) toCovariantClassMulLE [NonUnitalNonAssocSemiring α]
    [LE α] [CanonicallyOrderedAdd α] : CovariantClass α α (· * ·) (· ≤ ·) := by
  refine ⟨fun a b c h => ?_⟩
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [mul_add]
  apply self_le_add_right
#align canonically_ordered_comm_semiring.to_covariant_mul_le CanonicallyOrderedAdd.toCovariantClassMulLE

variable [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]

-- see Note [lower instance priority]
instance (priority := 100) toOrderedCommMonoid : OrderedCommMonoid α where
  mul_le_mul_left _ _ := mul_le_mul_left'
#align canonically_ordered_comm_semiring.to_ordered_comm_monoid CanonicallyOrderedAdd.toOrderedCommMonoid

@[nolint docBlame]
abbrev toOrderedCommSemiring : OrderedCommSemiring α where
  mul_comm := mul_comm
  zero_le_one := zero_le _
  add_le_add_left _ _ := add_le_add_left
  mul_le_mul_of_nonneg_left := fun _ _ _ h _ => mul_le_mul_left' h _
  mul_le_mul_of_nonneg_right := fun _ _ _ h _ => mul_le_mul_right' h _
#align canonically_ordered_comm_semiring.to_ordered_comm_semiring CanonicallyOrderedAdd.toOrderedCommSemiring

@[simp]
protected theorem mul_pos [NoZeroDivisors α] {a b : α} :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]
#align canonically_ordered_comm_semiring.mul_pos CanonicallyOrderedAdd.mul_pos

protected lemma mul_lt_mul_of_lt_of_lt
    [PosMulStrictMono α] {a b c d : α} (hab : a < b) (hcd : c < d) :
    a * c < b * d := by
  -- TODO: This should be an instance but it currently times out
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  obtain rfl | hc := eq_zero_or_pos c
  · rw [mul_zero]
    exact mul_pos ((zero_le _).trans_lt hab) hcd
  · exact mul_lt_mul_of_lt_of_lt' hab hcd ((zero_le _).trans_lt hab) hc

end CanonicallyOrderedAdd

section Sub

namespace AddLECancellable

protected theorem mul_tsub [NonUnitalNonAssocSemiring α] [PartialOrder α]
    [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)] {a b c : α}
    (h : AddLECancellable (a * c)) : a * (b - c) = a * b - a * c := by
  cases' total_of (· ≤ ·) b c with hbc hcb
  · rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_left' hbc a)]
  · apply h.eq_tsub_of_add_eq
    rw [← mul_add, tsub_add_cancel_of_le hcb]
#align add_le_cancellable.mul_tsub AddLECancellable.mul_tsub

protected theorem tsub_mul [NonUnitalNonAssocSemiring α] [PartialOrder α]
    [CanonicallyOrderedAdd α] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)] {a b c : α}
    (h : AddLECancellable (b * c)) : (a - b) * c = a * c - b * c := by
  cases' total_of (· ≤ ·) a b with hab hba
  · rw [tsub_eq_zero_iff_le.2 hab, zero_mul, tsub_eq_zero_iff_le.2 (mul_le_mul_right' hab c)]
  · apply h.eq_tsub_of_add_eq
    rw [← add_mul, tsub_add_cancel_of_le hba]
#align add_le_cancellable.tsub_mul AddLECancellable.tsub_mul

end AddLECancellable

theorem mul_tsub [NonUnitalNonAssocSemiring α] [PartialOrder α]
    [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)] [ContravariantClass α α (· + ·) (· ≤ ·)]
    (a b c : α) : a * (b - c) = a * b - a * c :=
  Contravariant.AddLECancellable.mul_tsub
#align mul_tsub mul_tsub

theorem tsub_mul [NonUnitalNonAssocSemiring α] [PartialOrder α]
    [CanonicallyOrderedAdd α] [CovariantClass α α (swap (· * ·)) (· ≤ ·)]
    [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)] [ContravariantClass α α (· + ·) (· ≤ ·)]
    (a b c : α) : (a - b) * c = a * c - b * c :=
  Contravariant.AddLECancellable.tsub_mul
#align tsub_mul tsub_mul

end Sub
