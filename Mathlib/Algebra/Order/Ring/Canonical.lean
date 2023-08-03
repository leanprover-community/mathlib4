/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Sub.Canonical
import Mathlib.GroupTheory.GroupAction.Defs

#align_import algebra.order.ring.canonical from "leanprover-community/mathlib"@"824f9ae93a4f5174d2ea948e2d75843dd83447bb"

/-!
# Canonically ordered rings and semirings.

-/


open Function

universe u

variable {α : Type u} {β : Type _}

section StrictOrderedSemiring

variable [StrictOrderedSemiring α] {a b c d : α}

section ExistsAddOfLE

variable [ExistsAddOfLE α]

/-- Binary **rearrangement inequality**. -/
theorem mul_add_mul_le_mul_add_mul (hab : a ≤ b) (hcd : c ≤ d) : a * d + b * c ≤ a * c + b * d := by
  obtain ⟨b, rfl⟩ := exists_add_of_le hab
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  exact add_le_add_left (mul_le_mul_of_nonneg_right hab <| (le_add_iff_nonneg_right _).1 hcd) _
#align mul_add_mul_le_mul_add_mul mul_add_mul_le_mul_add_mul

/-- Binary **rearrangement inequality**. -/
theorem mul_add_mul_le_mul_add_mul' (hba : b ≤ a) (hdc : d ≤ c) :
    a • d + b • c ≤ a • c + b • d := by
  rw [add_comm (a • d), add_comm (a • c)]
  exact mul_add_mul_le_mul_add_mul hba hdc
#align mul_add_mul_le_mul_add_mul' mul_add_mul_le_mul_add_mul'

/-- Binary strict **rearrangement inequality**. -/
theorem mul_add_mul_lt_mul_add_mul (hab : a < b) (hcd : c < d) : a * d + b * c < a * c + b * d := by
  obtain ⟨b, rfl⟩ := exists_add_of_le hab.le
  obtain ⟨d, rfl⟩ := exists_add_of_le hcd.le
  rw [mul_add, add_right_comm, mul_add, ← add_assoc]
  exact add_lt_add_left (mul_lt_mul_of_pos_right hab <| (lt_add_iff_pos_right _).1 hcd) _
#align mul_add_mul_lt_mul_add_mul mul_add_mul_lt_mul_add_mul

/-- Binary **rearrangement inequality**. -/
theorem mul_add_mul_lt_mul_add_mul' (hba : b < a) (hdc : d < c) :
    a • d + b • c < a • c + b • d := by
  rw [add_comm (a • d), add_comm (a • c)]
  exact mul_add_mul_lt_mul_add_mul hba hdc
#align mul_add_mul_lt_mul_add_mul' mul_add_mul_lt_mul_add_mul'

end ExistsAddOfLE

end StrictOrderedSemiring

namespace CanonicallyOrderedAdd

-- see Note [lower instance priority]
instance (priority := 100) toCovariantClassMulLE
    [Mul α] [Add α] [LeftDistribClass α] [LE α] [CanonicallyOrderedAdd α] :
    CovariantClass α α (· * ·) (· ≤ ·) := by
  refine' ⟨fun a b c h => _⟩
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [mul_add]
  apply self_le_add_right
#align canonically_ordered_comm_semiring.to_covariant_mul_le CanonicallyOrderedAdd.toCovariantClassMulLE

-- see Note [lower instance priority]
instance (priority := 100) toOrderedCommMonoid
    [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α] :
    OrderedCommMonoid α where
  mul_le_mul_left _ _ := mul_le_mul_left'
#align canonically_ordered_comm_semiring.to_ordered_comm_monoid CanonicallyOrderedAdd.toOrderedCommMonoid

-- see Note [lower instance priority]
instance (priority := 100) toOrderedCommSemiring
    [CommSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [CovariantClass α α (· + ·) (· ≤ ·)] :
    OrderedCommSemiring α where
  mul_comm := mul_comm
  zero_le_one := zero_le _
  add_le_add_left _ _ := add_le_add_left
  mul_le_mul_of_nonneg_left := fun _ _ _ h _ => mul_le_mul_left' h _
  mul_le_mul_of_nonneg_right := fun _ _ _ h _ => mul_le_mul_right' h _
#align canonically_ordered_comm_semiring.to_ordered_comm_semiring CanonicallyOrderedAdd.toOrderedCommSemiring
--[OrderedSemiring α] [CanonicallyOrderedAdd α]
@[simp]
theorem mul_pos [NonUnitalNonAssocSemiring α] [PartialOrder α] [CanonicallyOrderedAdd α]
    [NoZeroDivisors α] {a b : α} :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]
#align canonically_ordered_comm_semiring.mul_pos CanonicallyOrderedAdd.mul_pos

end CanonicallyOrderedAdd

section Sub

namespace AddLECancellable

protected theorem mul_tsub [OrderedSemiring α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)] {a b c : α}
    (h : AddLECancellable (a * c)) : a * (b - c) = a * b - a * c := by
  cases' total_of (· ≤ ·) b c with hbc hcb
  · rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_left' hbc a)]
  · apply h.eq_tsub_of_add_eq
    rw [← mul_add, tsub_add_cancel_of_le hcb]
#align add_le_cancellable.mul_tsub AddLECancellable.mul_tsub

protected theorem tsub_mul [OrderedCommSemiring α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)] {a b c : α}
    (h : AddLECancellable (b * c)) : (a - b) * c = a * c - b * c := by
  simp only [mul_comm _ c] at *
  exact h.mul_tsub
#align add_le_cancellable.tsub_mul AddLECancellable.tsub_mul

end AddLECancellable

theorem mul_tsub [OrderedSemiring α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)] [ContravariantClass α α (· + ·) (· ≤ ·)]
    (a b c : α) : a * (b - c) = a * b - a * c :=
  Contravariant.AddLECancellable.mul_tsub
#align mul_tsub mul_tsub

theorem tsub_mul [OrderedCommSemiring α] [CanonicallyOrderedAdd α]
    [Sub α] [OrderedSub α] [IsTotal α (· ≤ ·)] [ContravariantClass α α (· + ·) (· ≤ ·)]
    (a b c : α) : (a - b) * c = a * c - b * c :=
  Contravariant.AddLECancellable.tsub_mul
#align tsub_mul tsub_mul

end Sub
