/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Ring.Semiconj
import Mathlib.Algebra.Ring.Units
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Data.Bracket

#align_import algebra.ring.commute from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `Mathlib.Algebra.Group.Basic`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `Mathlib.Algebra.Ring.Defs`.

-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

namespace Commute

@[simp]
theorem add_right [Distrib R] {a b c : R} : Commute a b → Commute a c → Commute a (b + c) :=
  SemiconjBy.add_right
#align commute.add_right Commute.add_rightₓ
-- for some reason mathport expected `Semiring` instead of `Distrib`?

@[simp]
theorem add_left [Distrib R] {a b c : R} : Commute a c → Commute b c → Commute (a + b) c :=
  SemiconjBy.add_left
#align commute.add_left Commute.add_leftₓ
-- for some reason mathport expected `Semiring` instead of `Distrib`?

section deprecated
set_option linter.deprecated false

@[deprecated (since := "2022-11-28")]
theorem bit0_right [Distrib R] {x y : R} (h : Commute x y) : Commute x (bit0 y) :=
  h.add_right h
#align commute.bit0_right Commute.bit0_right

@[deprecated (since := "2022-11-28")]
theorem bit0_left [Distrib R] {x y : R} (h : Commute x y) : Commute (bit0 x) y :=
  h.add_left h
#align commute.bit0_left Commute.bit0_left

@[deprecated (since := "2022-11-28")]
theorem bit1_right [NonAssocSemiring R] {x y : R} (h : Commute x y) : Commute x (bit1 y) :=
  h.bit0_right.add_right (Commute.one_right x)
#align commute.bit1_right Commute.bit1_right

@[deprecated (since := "2022-11-28")]
theorem bit1_left [NonAssocSemiring R] {x y : R} (h : Commute x y) : Commute (bit1 x) y :=
  h.bit0_left.add_left (Commute.one_left y)
#align commute.bit1_left Commute.bit1_left

end deprecated

/-- Representation of a difference of two squares of commuting elements as a product. -/
theorem mul_self_sub_mul_self_eq [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a + b) * (a - b) := by
  rw [add_mul, mul_sub, mul_sub, h.eq, sub_add_sub_cancel]
#align commute.mul_self_sub_mul_self_eq Commute.mul_self_sub_mul_self_eq

theorem mul_self_sub_mul_self_eq' [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a - b) * (a + b) := by
  rw [mul_add, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]
#align commute.mul_self_sub_mul_self_eq' Commute.mul_self_sub_mul_self_eq'

theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R}
    (h : Commute a b) : a * a = b * b ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.mul_self_sub_mul_self_eq, mul_eq_zero, or_comm, sub_eq_zero,
    add_eq_zero_iff_eq_neg]
#align commute.mul_self_eq_mul_self_iff Commute.mul_self_eq_mul_self_iff

section

variable [Mul R] [HasDistribNeg R] {a b : R}

theorem neg_right : Commute a b → Commute a (-b) :=
  SemiconjBy.neg_right
#align commute.neg_right Commute.neg_right

@[simp]
theorem neg_right_iff : Commute a (-b) ↔ Commute a b :=
  SemiconjBy.neg_right_iff
#align commute.neg_right_iff Commute.neg_right_iff

theorem neg_left : Commute a b → Commute (-a) b :=
  SemiconjBy.neg_left
#align commute.neg_left Commute.neg_left

@[simp]
theorem neg_left_iff : Commute (-a) b ↔ Commute a b :=
  SemiconjBy.neg_left_iff
#align commute.neg_left_iff Commute.neg_left_iff

end

section

variable [MulOneClass R] [HasDistribNeg R] {a : R}

-- Porting note (#10618): no longer needs to be `@[simp]` since `simp` can prove it.
-- @[simp]
theorem neg_one_right (a : R) : Commute a (-1) :=
  SemiconjBy.neg_one_right a
#align commute.neg_one_right Commute.neg_one_right

-- Porting note (#10618): no longer needs to be `@[simp]` since `simp` can prove it.
-- @[simp]
theorem neg_one_left (a : R) : Commute (-1) a :=
  SemiconjBy.neg_one_left a
#align commute.neg_one_left Commute.neg_one_left

end

section

variable [NonUnitalNonAssocRing R] {a b c : R}

@[simp]
theorem sub_right : Commute a b → Commute a c → Commute a (b - c) :=
  SemiconjBy.sub_right
#align commute.sub_right Commute.sub_right

@[simp]
theorem sub_left : Commute a c → Commute b c → Commute (a - b) c :=
  SemiconjBy.sub_left
#align commute.sub_left Commute.sub_left

end

section Ring
variable [Ring R] {a b : R}

protected lemma sq_sub_sq (h : Commute a b) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq, h.mul_self_sub_mul_self_eq]
#align commute.sq_sub_sq Commute.sq_sub_sq

variable [NoZeroDivisors R]

protected lemma sq_eq_sq_iff_eq_or_eq_neg (h : Commute a b) : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, or_comm]
#align commute.sq_eq_sq_iff_eq_or_eq_neg Commute.sq_eq_sq_iff_eq_or_eq_neg

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
#align neg_one_pow_eq_or neg_one_pow_eq_or

variable {R}

lemma neg_pow (a : R) (n : ℕ) : (-a) ^ n = (-1) ^ n * a ^ n :=
  neg_one_mul a ▸ (Commute.neg_one_left a).mul_pow n
#align neg_pow neg_pow

lemma neg_pow' (a : R) (n : ℕ) : (-a) ^ n = a ^ n * (-1) ^ n :=
  mul_neg_one a ▸ (Commute.neg_one_right a).mul_pow n

section
set_option linter.deprecated false

lemma neg_pow_bit0 (a : R) (n : ℕ) : (-a) ^ bit0 n = a ^ bit0 n := by
  rw [pow_bit0', neg_mul_neg, pow_bit0']
#align neg_pow_bit0 neg_pow_bit0

@[simp]
lemma neg_pow_bit1 (a : R) (n : ℕ) : (-a) ^ bit1 n = -a ^ bit1 n := by
  simp only [bit1, pow_succ', neg_pow_bit0, neg_mul_eq_neg_mul]
#align neg_pow_bit1 neg_pow_bit1

end

lemma neg_sq (a : R) : (-a) ^ 2 = a ^ 2 := by simp [sq]
#align neg_sq neg_sq

-- Porting note: removed the simp attribute to please the simpNF linter
lemma neg_one_sq : (-1 : R) ^ 2 = 1 := by simp [neg_sq, one_pow]
#align neg_one_sq neg_one_sq

alias neg_pow_two := neg_sq
#align neg_pow_two neg_pow_two

alias neg_one_pow_two := neg_one_sq
#align neg_one_pow_two neg_one_pow_two

end HasDistribNeg

section Ring
variable [Ring R] {a b : R} {n : ℕ}

@[simp] lemma neg_one_pow_mul_eq_zero_iff : (-1) ^ n * a = 0 ↔ a = 0 := by
  rcases neg_one_pow_eq_or R n with h | h <;> simp [h]
#align neg_one_pow_mul_eq_zero_iff neg_one_pow_mul_eq_zero_iff

@[simp] lemma mul_neg_one_pow_eq_zero_iff : a * (-1) ^ n = 0 ↔ a = 0 := by
  obtain h | h := neg_one_pow_eq_or R n <;> simp [h]
#align mul_neg_one_pow_eq_zero_iff mul_neg_one_pow_eq_zero_iff

variable [NoZeroDivisors R]

@[simp] lemma sq_eq_one_iff : a ^ 2 = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).sq_eq_sq_iff_eq_or_eq_neg, one_pow]
#align sq_eq_one_iff sq_eq_one_iff

lemma sq_ne_one_iff : a ^ 2 ≠ 1 ↔ a ≠ 1 ∧ a ≠ -1 := sq_eq_one_iff.not.trans not_or
#align sq_ne_one_iff sq_ne_one_iff

lemma neg_one_pow_eq_pow_mod_two (n : ℕ) : (-1 : R) ^ n = (-1) ^ (n % 2) := by
  rw [← Nat.mod_add_div n 2, pow_add, pow_mul]; simp [sq]
#align neg_one_pow_eq_pow_mod_two neg_one_pow_eq_pow_mod_two

end Ring

/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self [CommRing R] (a b : R) : a * a - b * b = (a + b) * (a - b) :=
  (Commute.all a b).mul_self_sub_mul_self_eq
#align mul_self_sub_mul_self mul_self_sub_mul_self

theorem mul_self_sub_one [NonAssocRing R] (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← (Commute.one_right a).mul_self_sub_mul_self_eq, mul_one]
#align mul_self_sub_one mul_self_sub_one

theorem mul_self_eq_mul_self_iff [CommRing R] [NoZeroDivisors R] {a b : R} :
    a * a = b * b ↔ a = b ∨ a = -b :=
  (Commute.all a b).mul_self_eq_mul_self_iff
#align mul_self_eq_mul_self_iff mul_self_eq_mul_self_iff

theorem mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisors R] {a : R} :
    a * a = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).mul_self_eq_mul_self_iff, mul_one]
#align mul_self_eq_one_iff mul_self_eq_one_iff

section CommRing
variable [CommRing R]

lemma sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := (Commute.all a b).sq_sub_sq
#align sq_sub_sq sq_sub_sq

alias pow_two_sub_pow_two := sq_sub_sq
#align pow_two_sub_pow_two pow_two_sub_pow_two

lemma sub_sq (a b : R) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  rw [sub_eq_add_neg, add_sq, neg_sq, mul_neg, ← sub_eq_add_neg]
#align sub_sq sub_sq

alias sub_pow_two := sub_sq
#align sub_pow_two sub_pow_two

lemma sub_sq' (a b : R) : (a - b) ^ 2 = a ^ 2 + b ^ 2 - 2 * a * b := by
  rw [sub_eq_add_neg, add_sq', neg_sq, mul_neg, ← sub_eq_add_neg]
#align sub_sq' sub_sq'

variable [NoZeroDivisors R] {a b : R}

lemma sq_eq_sq_iff_eq_or_eq_neg : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b :=
  (Commute.all a b).sq_eq_sq_iff_eq_or_eq_neg
#align sq_eq_sq_iff_eq_or_eq_neg sq_eq_sq_iff_eq_or_eq_neg

lemma eq_or_eq_neg_of_sq_eq_sq (a b : R) : a ^ 2 = b ^ 2 → a = b ∨ a = -b :=
  sq_eq_sq_iff_eq_or_eq_neg.1
#align eq_or_eq_neg_of_sq_eq_sq eq_or_eq_neg_of_sq_eq_sq

-- Copies of the above CommRing lemmas for `Units R`.
namespace Units

protected lemma sq_eq_sq_iff_eq_or_eq_neg {a b : Rˣ} : a ^ 2 = b ^ 2 ↔ a = b ∨ a = -b := by
  simp_rw [ext_iff, val_pow_eq_pow_val, sq_eq_sq_iff_eq_or_eq_neg, Units.val_neg]
#align units.sq_eq_sq_iff_eq_or_eq_neg Units.sq_eq_sq_iff_eq_or_eq_neg

protected lemma eq_or_eq_neg_of_sq_eq_sq (a b : Rˣ) (h : a ^ 2 = b ^ 2) : a = b ∨ a = -b :=
  Units.sq_eq_sq_iff_eq_or_eq_neg.1 h
#align units.eq_or_eq_neg_of_sq_eq_sq Units.eq_or_eq_neg_of_sq_eq_sq

end Units
end CommRing

namespace Units

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
theorem inv_eq_self_iff [Ring R] [NoZeroDivisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 := by
  rw [inv_eq_iff_mul_eq_one]
  simp only [ext_iff]
  push_cast
  exact mul_self_eq_one_iff
#align units.inv_eq_self_iff Units.inv_eq_self_iff

end Units

section Bracket

variable [NonUnitalNonAssocRing R]

namespace Ring

instance (priority := 100) instBracket : Bracket R R := ⟨fun x y => x * y - y * x⟩

theorem lie_def (x y : R) : ⁅x, y⁆ = x * y - y * x := rfl
#align ring.lie_def Ring.lie_def

end Ring

theorem commute_iff_lie_eq {x y : R} : Commute x y ↔ ⁅x, y⁆ = 0 := sub_eq_zero.symm
#align commute_iff_lie_eq commute_iff_lie_eq

theorem Commute.lie_eq {x y : R} (h : Commute x y) : ⁅x, y⁆ = 0 := sub_eq_zero_of_eq h
#align commute.lie_eq Commute.lie_eq

end Bracket
