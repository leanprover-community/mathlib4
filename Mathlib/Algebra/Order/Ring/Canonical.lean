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

* `CanonicallyOrderedCommSemiring`
  - `CanonicallyOrderedAddCommMonoid` & multiplication & `*` respects `≤` & no zero divisors
  - `CommSemiring` & `a ≤ b ↔ ∃ c, b = a + c` & no zero divisors

## TODO

We're still missing some typeclasses, like
* `CanonicallyOrderedSemiring`
They have yet to come up in practice.
-/


open Function

universe u

variable {α : Type u} {β : Type*}

/-- A canonically ordered commutative semiring is an ordered, commutative semiring in which `a ≤ b`
iff there exists `c` with `b = a + c`. This is satisfied by the natural numbers, for example, but
not the integers or other ordered groups. -/
class CanonicallyOrderedCommSemiring (α : Type*) extends CanonicallyOrderedAddCommMonoid α,
    CommSemiring α where
  /-- No zero divisors. -/
  protected eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : α}, a * b = 0 → a = 0 ∨ b = 0
#align canonically_ordered_comm_semiring CanonicallyOrderedCommSemiring

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

namespace CanonicallyOrderedCommSemiring

variable [CanonicallyOrderedCommSemiring α] {a b : α}

-- see Note [lower instance priority]
instance (priority := 100) toNoZeroDivisors : NoZeroDivisors α :=
  ⟨CanonicallyOrderedCommSemiring.eq_zero_or_eq_zero_of_mul_eq_zero⟩
#align canonically_ordered_comm_semiring.to_no_zero_divisors CanonicallyOrderedCommSemiring.toNoZeroDivisors

-- see Note [lower instance priority]
instance (priority := 100) toCovariantClassMulLE : CovariantClass α α (· * ·) (· ≤ ·) := by
  refine' ⟨fun a b c h => _⟩
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [mul_add]
  apply self_le_add_right
#align canonically_ordered_comm_semiring.to_covariant_mul_le CanonicallyOrderedCommSemiring.toCovariantClassMulLE

-- see Note [lower instance priority]
instance (priority := 100) toOrderedCommMonoid : OrderedCommMonoid α where
  mul_le_mul_left := fun _ _ => mul_le_mul_left'
#align canonically_ordered_comm_semiring.to_ordered_comm_monoid CanonicallyOrderedCommSemiring.toOrderedCommMonoid

-- see Note [lower instance priority]
instance (priority := 100) toOrderedCommSemiring : OrderedCommSemiring α :=
  { ‹CanonicallyOrderedCommSemiring α› with
    zero_le_one := zero_le _,
    mul_le_mul_of_nonneg_left := fun a b c h _ => mul_le_mul_left' h _,
    mul_le_mul_of_nonneg_right := fun a b c h _ => mul_le_mul_right' h _ }
#align canonically_ordered_comm_semiring.to_ordered_comm_semiring CanonicallyOrderedCommSemiring.toOrderedCommSemiring

@[simp]
theorem mul_pos : 0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]
#align canonically_ordered_comm_semiring.mul_pos CanonicallyOrderedCommSemiring.mul_pos

end CanonicallyOrderedCommSemiring

section Sub

variable [CanonicallyOrderedCommSemiring α] {a b c : α}

variable [Sub α] [OrderedSub α]

variable [IsTotal α (· ≤ ·)]

namespace AddLECancellable

protected theorem mul_tsub (h : AddLECancellable (a * c)) : a * (b - c) = a * b - a * c := by
  cases' total_of (· ≤ ·) b c with hbc hcb
  · rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_left' hbc a)]
  · apply h.eq_tsub_of_add_eq
    rw [← mul_add, tsub_add_cancel_of_le hcb]
#align add_le_cancellable.mul_tsub AddLECancellable.mul_tsub

protected theorem tsub_mul (h : AddLECancellable (b * c)) : (a - b) * c = a * c - b * c := by
  simp only [mul_comm _ c] at *
  exact h.mul_tsub
#align add_le_cancellable.tsub_mul AddLECancellable.tsub_mul

end AddLECancellable

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem mul_tsub (a b c : α) : a * (b - c) = a * b - a * c :=
  Contravariant.AddLECancellable.mul_tsub
#align mul_tsub mul_tsub

theorem tsub_mul (a b c : α) : (a - b) * c = a * c - b * c :=
  Contravariant.AddLECancellable.tsub_mul
#align tsub_mul tsub_mul

end Sub
