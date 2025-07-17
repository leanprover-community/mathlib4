/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Ring.Semiconj
import Mathlib.Algebra.Ring.Units
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Data.Bracket

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `Mathlib/Algebra/Group/Basic.lean`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `Mathlib/Algebra/Ring/Defs.lean`.

-/


universe u

variable {R : Type u}

open Function

namespace Commute

@[simp]
theorem add_right [Distrib R] {a b c : R} : Commute a b → Commute a c → Commute a (b + c) :=
  SemiconjBy.add_right
-- for some reason mathport expected `Semiring` instead of `Distrib`?

@[simp]
theorem add_left [Distrib R] {a b c : R} : Commute a c → Commute b c → Commute (a + b) c :=
  SemiconjBy.add_left
-- for some reason mathport expected `Semiring` instead of `Distrib`?

/-- Representation of a difference of two squares of commuting elements as a product. -/
theorem mul_self_sub_mul_self_eq [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a + b) * (a - b) := by
  rw [add_mul, mul_sub, mul_sub, h.eq, sub_add_sub_cancel]

theorem mul_self_sub_mul_self_eq' [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a - b) * (a + b) := by
  rw [mul_add, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]

theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R}
    (h : Commute a b) : a * a = b * b ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.mul_self_sub_mul_self_eq, mul_eq_zero, or_comm, sub_eq_zero,
    add_eq_zero_iff_eq_neg]

section

variable [Mul R] [HasDistribNeg R] {a b : R}

theorem neg_right : Commute a b → Commute a (-b) :=
  SemiconjBy.neg_right

@[simp]
theorem neg_right_iff : Commute a (-b) ↔ Commute a b :=
  SemiconjBy.neg_right_iff

theorem neg_left : Commute a b → Commute (-a) b :=
  SemiconjBy.neg_left

@[simp]
theorem neg_left_iff : Commute (-a) b ↔ Commute a b :=
  SemiconjBy.neg_left_iff

end

section

variable [MulOneClass R] [HasDistribNeg R]

theorem neg_one_right (a : R) : Commute a (-1) :=
  SemiconjBy.neg_one_right a

theorem neg_one_left (a : R) : Commute (-1) a :=
  SemiconjBy.neg_one_left a

end

section

variable [NonUnitalNonAssocRing R] {a b c : R}

@[simp]
theorem sub_right : Commute a b → Commute a c → Commute a (b - c) :=
  SemiconjBy.sub_right

@[simp]
theorem sub_left : Commute a c → Commute b c → Commute (a - b) c :=
  SemiconjBy.sub_left

end

section Ring
variable [Ring R] {a b : R}

protected lemma sq_sub_sq (h : Commute a b) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq, h.mul_self_sub_mul_self_eq]

variable [NoZeroDivisors R]

protected lemma sq_eq_sq_iff_eq_or_eq_neg (h : Commute a b) : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, or_comm]

end Ring
end Commute

section HasDistribNeg
variable (R)
variable [Monoid R] [HasDistribNeg R]

lemma neg_one_pow_eq_or : ∀ n : ℕ, (-1 : R) ^ n = 1 ∨ (-1 : R) ^ n = -1
  | 0 => Or.inl (pow_zero _)
  | n + 1 => (neg_one_pow_eq_or n).symm.imp
    (fun h ↦ by rw [pow_succ, h, neg_one_mul, neg_neg])
    (fun h ↦ by rw [pow_succ, h, one_mul])

variable {R}

lemma neg_pow (a : R) (n : ℕ) : (-a) ^ n = (-1) ^ n * a ^ n :=
  neg_one_mul a ▸ (Commute.neg_one_left a).mul_pow n

lemma neg_pow' (a : R) (n : ℕ) : (-a) ^ n = a ^ n * (-1) ^ n :=
  mul_neg_one a ▸ (Commute.neg_one_right a).mul_pow n

lemma neg_sq (a : R) : (-a) ^ 2 = a ^ 2 := by simp [sq]

lemma neg_one_sq : (-1 : R) ^ 2 = 1 := by simp [neg_sq, one_pow]

alias neg_pow_two := neg_sq

alias neg_one_pow_two := neg_one_sq

end HasDistribNeg

section Ring
variable [Ring R] {a : R} {n : ℕ}

@[simp] lemma neg_one_pow_mul_eq_zero_iff : (-1) ^ n * a = 0 ↔ a = 0 := by
  rcases neg_one_pow_eq_or R n with h | h <;> simp [h]

@[simp] lemma mul_neg_one_pow_eq_zero_iff : a * (-1) ^ n = 0 ↔ a = 0 := by
  obtain h | h := neg_one_pow_eq_or R n <;> simp [h]

lemma neg_one_pow_eq_pow_mod_two (n : ℕ) : (-1 : R) ^ n = (-1) ^ (n % 2) := by
  rw [← Nat.mod_add_div n 2, pow_add, pow_mul]; simp [sq]

variable [NoZeroDivisors R]

@[simp] lemma sq_eq_one_iff : a ^ 2 = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).sq_eq_sq_iff_eq_or_eq_neg, one_pow]

lemma sq_ne_one_iff : a ^ 2 ≠ 1 ↔ a ≠ 1 ∧ a ≠ -1 := sq_eq_one_iff.not.trans not_or

end Ring

/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self [NonUnitalNonAssocCommRing R] (a b : R) :
    a * a - b * b = (a + b) * (a - b) :=
  (Commute.all a b).mul_self_sub_mul_self_eq

theorem mul_self_sub_one [NonAssocRing R] (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← (Commute.one_right a).mul_self_sub_mul_self_eq, mul_one]

theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocCommRing R] [NoZeroDivisors R] {a b : R} :
    a * a = b * b ↔ a = b ∨ a = -b :=
  (Commute.all a b).mul_self_eq_mul_self_iff

theorem mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisors R] {a : R} :
    a * a = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).mul_self_eq_mul_self_iff, mul_one]

section CommRing
variable [CommRing R]

lemma sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := (Commute.all a b).sq_sub_sq

alias pow_two_sub_pow_two := sq_sub_sq

lemma sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  rw [sub_eq_add_neg, add_sq, neg_sq, mul_neg, ← sub_eq_add_neg]

alias sub_pow_two := sub_sq

lemma sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
  rw [sub_eq_add_neg, add_sq', neg_sq, mul_neg, ← sub_eq_add_neg]

lemma sub_sq_comm (a b : R) : (a - b) ^ 2 = (b - a) ^ 2 := by
  rw [sub_sq', mul_right_comm, add_comm, sub_sq']

variable [NoZeroDivisors R] {a b : R}

lemma sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
  (Commute.all a b).sq_eq_sq_iff_eq_or_eq_neg

lemma eq_or_eq_neg_of_sq_eq_sq (a b : R) : a ^ 2 = b ^ 2 → a = b ∨ a = -b :=
  sq_eq_sq_iff_eq_or_eq_neg.1

-- Copies of the above CommRing lemmas for `Units R`.
namespace Units

protected lemma sq_eq_sq_iff_eq_or_eq_neg {a b : Rˣ} : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  simp_rw [Units.ext_iff, val_pow_eq_pow_val, sq_eq_sq_iff_eq_or_eq_neg, Units.val_neg]

protected lemma eq_or_eq_neg_of_sq_eq_sq (a b : Rˣ) (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b :=
  Units.sq_eq_sq_iff_eq_or_eq_neg.1 h

end Units
end CommRing

namespace Units

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
theorem inv_eq_self_iff [Ring R] [NoZeroDivisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 := by
  rw [inv_eq_iff_mul_eq_one]
  simp only [Units.ext_iff]
  push_cast
  exact mul_self_eq_one_iff

end Units

section Bracket

variable [NonUnitalNonAssocRing R]

namespace Ring

instance (priority := 100) instBracket : Bracket R R := ⟨fun x y => x * y - y * x⟩

theorem lie_def (x y : R) : ⁅x, y⁆ = x * y - y * x := rfl

end Ring

theorem commute_iff_lie_eq {x y : R} : Commute x y ↔ ⁅x, y⁆ = 0 := sub_eq_zero.symm

theorem Commute.lie_eq {x y : R} (h : Commute x y) : ⁅x, y⁆ = 0 := sub_eq_zero_of_eq h

end Bracket
