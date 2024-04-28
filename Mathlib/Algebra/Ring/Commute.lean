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

@[deprecated]
theorem bit0_right [Distrib R] {x y : R} (h : Commute x y) : Commute x (bit0 y) :=
  h.add_right h
#align commute.bit0_right Commute.bit0_right

@[deprecated]
theorem bit0_left [Distrib R] {x y : R} (h : Commute x y) : Commute (bit0 x) y :=
  h.add_left h
#align commute.bit0_left Commute.bit0_left

@[deprecated]
theorem bit1_right [NonAssocSemiring R] {x y : R} (h : Commute x y) : Commute x (bit1 y) :=
  h.bit0_right.add_right (Commute.one_right x)
#align commute.bit1_right Commute.bit1_right

@[deprecated]
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

end Commute

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
