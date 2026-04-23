/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Util.CompileInductive

/-!
# Canonically ordered rings and semirings.
-/

@[expose] public section


open Function

universe u

variable {R : Type u}

-- see Note [lower instance priority]
instance (priority := 10) CanonicallyOrderedAdd.toZeroLEOneClass
    [AddZeroClass R] [One R] [LE R] [CanonicallyOrderedAdd R] : ZeroLEOneClass R where
  zero_le_one := zero_le _

-- this holds more generally if we refactor `Odd` to use
-- either `2 • t` or `t + t` instead of `2 * t`.
lemma Odd.pos [Semiring R] [PartialOrder R] [CanonicallyOrderedAdd R] [Nontrivial R] {a : R} :
    Odd a → 0 < a := by
  rintro ⟨k, rfl⟩; simp

namespace CanonicallyOrderedAdd

-- see Note [lower instance priority]
instance (priority := 100) toMulLeftMono [NonUnitalNonAssocSemiring R]
    [LE R] [CanonicallyOrderedAdd R] : MulLeftMono R := by
  refine ⟨fun a b c h => ?_⟩
  dsimp
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [mul_add]
  apply self_le_add_right

-- see Note [lower instance priority]
instance (priority := 100) toMulRightMono [NonUnitalNonAssocSemiring R]
    [LE R] [CanonicallyOrderedAdd R] : MulRightMono R := by
  refine ⟨fun a b c h => ?_⟩
  dsimp [swap]
  rcases exists_add_of_le h with ⟨c, rfl⟩
  rw [add_mul]
  apply self_le_add_right

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]

-- TODO: make it an instance
lemma toIsOrderedMonoid : IsOrderedMonoid R where
  mul_le_mul_left _ _ := mul_le_mul_left

-- TODO: make it an instance
lemma toIsOrderedRing : IsOrderedRing R where
  add_le_add_left _ _ := add_le_add_left

@[simp]
protected theorem mul_pos [NoZeroDivisors R] {a b : R} :
    0 < a * b ↔ 0 < a ∧ 0 < b := by
  simp only [pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]

lemma pow_pos [NoZeroDivisors R] {a : R} (ha : 0 < a) (n : ℕ) : 0 < a ^ n :=
  pos_iff_ne_zero.2 <| pow_ne_zero _ ha.ne'

protected lemma mul_lt_mul_of_lt_of_lt
    [PosMulStrictMono R] {a b c d : R} (hab : a < b) (hcd : c < d) :
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

variable [NonUnitalNonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)]

namespace AddLECancellable

protected theorem mul_tsub {a b c : R}
    (h : AddLECancellable (a * c)) : a * (b - c) = a * b - a * c := by
  obtain (hbc | hcb) := total_of (· ≤ ·) b c
  · rw [tsub_eq_zero_iff_le.2 hbc, mul_zero, tsub_eq_zero_iff_le.2 (mul_le_mul_right hbc a)]
  · apply h.eq_tsub_of_add_eq
    rw [← mul_add, tsub_add_cancel_of_le hcb]

protected theorem tsub_mul [MulRightMono R] {a b c : R}
    (h : AddLECancellable (b * c)) : (a - b) * c = a * c - b * c := by
  obtain (hab | hba) := total_of (· ≤ ·) a b
  · rw [tsub_eq_zero_iff_le.2 hab, zero_mul, tsub_eq_zero_iff_le.2 (mul_le_mul_left hab c)]
  · apply h.eq_tsub_of_add_eq
    rw [← add_mul, tsub_add_cancel_of_le hba]

end AddLECancellable

variable [AddLeftReflectLE R]

theorem mul_tsub (a b c : R) : a * (b - c) = a * b - a * c :=
  Contravariant.AddLECancellable.mul_tsub

theorem tsub_mul [MulRightMono R] (a b c : R) :
    (a - b) * c = a * c - b * c :=
  Contravariant.AddLECancellable.tsub_mul

end NonUnitalNonAssocSemiring

section NonAssocSemiring

variable [NonAssocSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)]

lemma mul_tsub_one [AddLeftReflectLE R] (a b : R) :
    a * (b - 1) = a * b - a := by rw [mul_tsub, mul_one]
lemma tsub_one_mul [MulRightMono R] [AddLeftReflectLE R] (a b : R) :
    (a - 1) * b = a * b - b := by rw [tsub_mul, one_mul]

end NonAssocSemiring

section CommSemiring

variable [CommSemiring R] [PartialOrder R] [CanonicallyOrderedAdd R]
  [Sub R] [OrderedSub R] [@Std.Total R (· ≤ ·)] [AddLeftReflectLE R]

/-- The `tsub` version of `mul_self_sub_mul_self`. Notably, this holds for `Nat` and `NNReal`. -/
theorem mul_self_tsub_mul_self (a b : R) :
    a * a - b * b = (a + b) * (a - b) := by
  rw [mul_tsub, add_mul, add_mul, tsub_add_eq_tsub_tsub, mul_comm b a, add_tsub_cancel_right]

/-- The `tsub` version of `sq_sub_sq`. Notably, this holds for `Nat` and `NNReal`. -/
theorem sq_tsub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq, mul_self_tsub_mul_self]

theorem mul_self_tsub_one (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← mul_self_tsub_mul_self, mul_one]

end CommSemiring

end Sub
