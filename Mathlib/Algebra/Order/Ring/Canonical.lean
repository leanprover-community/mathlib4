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

section CanonicallyOrderedCommSemiring
variable [CanonicallyOrderedCommSemiring α] {a b c d : α}

-- this holds more generally in a `CanonicallyOrderedAddCommMonoid` if we refactor `Odd` to use
-- either `2 • t` or `t + t` instead of `2 * t`.
lemma Odd.pos [Nontrivial α] : Odd a → 0 < a := by rintro ⟨k, rfl⟩; simp [pos_iff_ne_zero]

namespace CanonicallyOrderedCommSemiring

-- see Note [lower instance priority]
instance (priority := 100) toNoZeroDivisors : NoZeroDivisors α :=
  ⟨CanonicallyOrderedCommSemiring.eq_zero_or_eq_zero_of_mul_eq_zero⟩

-- see Note [lower instance priority]
instance (priority := 100) toCovariantClassMulLE : CovariantClass α α (· * ·) (· ≤ ·) := by
  refine ⟨fun a b c h => ?_⟩
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [mul_add]
  apply self_le_add_right

-- see Note [lower instance priority]
instance (priority := 100) toOrderedCommMonoid : OrderedCommMonoid α where
  mul_le_mul_left := fun _ _ => mul_le_mul_left'

-- see Note [lower instance priority]
instance (priority := 100) toOrderedCommSemiring : OrderedCommSemiring α :=
  { ‹CanonicallyOrderedCommSemiring α› with
    zero_le_one := zero_le _,
    mul_le_mul_of_nonneg_left := fun a b c h _ => mul_le_mul_left' h _,
    mul_le_mul_of_nonneg_right := fun a b c h _ => mul_le_mul_right' h _ }

@[simp]
protected theorem mul_pos : 0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]

lemma pow_pos (ha : 0 < a) (n : ℕ) : 0 < a ^ n := pos_iff_ne_zero.2 <| pow_ne_zero _ ha.ne'

protected lemma mul_lt_mul_of_lt_of_lt [PosMulStrictMono α] (hab : a < b) (hcd : c < d) :
    a * c < b * d := by
  -- TODO: This should be an instance but it currently times out
  have := posMulStrictMono_iff_mulPosStrictMono.1 ‹_›
  obtain rfl | hc := eq_zero_or_pos c
  · rw [mul_zero]
    exact mul_pos ((zero_le _).trans_lt hab) hcd
  · exact mul_lt_mul_of_pos' hab hcd hc ((zero_le _).trans_lt hab)

end CanonicallyOrderedCommSemiring
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

protected theorem tsub_mul (h : AddLECancellable (b * c)) : (a - b) * c = a * c - b * c := by
  simp only [mul_comm _ c] at *
  exact h.mul_tsub

end AddLECancellable

variable [ContravariantClass α α (· + ·) (· ≤ ·)]

theorem mul_tsub (a b c : α) : a * (b - c) = a * b - a * c :=
  Contravariant.AddLECancellable.mul_tsub

theorem tsub_mul (a b c : α) : (a - b) * c = a * c - b * c :=
  Contravariant.AddLECancellable.tsub_mul

lemma mul_tsub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_tsub, mul_one]
lemma tsub_one_mul (a b : α) : (a - 1) * b = a * b - b := by rw [tsub_mul, one_mul]

/-- The `tsub` version of `mul_self_sub_mul_self`. Notably, this holds for `Nat` and `NNReal`. -/
theorem mul_self_tsub_mul_self (a b : α) : a * a - b * b = (a + b) * (a - b) := by
  rw [mul_tsub, add_mul, add_mul, tsub_add_eq_tsub_tsub, mul_comm b a, add_tsub_cancel_right]

/-- The `tsub` version of `sq_sub_sq`. Notably, this holds for `Nat` and `NNReal`. -/
theorem sq_tsub_sq (a b : α) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq, mul_self_tsub_mul_self]

theorem mul_self_tsub_one (a : α) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← mul_self_tsub_mul_self, mul_one]

end Sub
