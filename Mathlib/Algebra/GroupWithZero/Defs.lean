/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Defs

/-!
# Typeclasses for groups with an adjoined zero element

This file provides just the typeclass definitions, and the projection lemmas that expose their
members.

## Main definitions

* `GroupWithZero`
* `CommGroupWithZero`
-/


universe u

-- We have to fix the universe of `G₀` here, since the default argument to
-- `GroupWithZero.div'` cannot contain a universe metavariable.
variable {G₀ : Type u} {M₀ M₀' G₀' : Type _}

theorem eq_of_sub_eq_zero' [AddGroup R] {a b : R} (h : a - b = 0) : a = b :=
  add_right_cancel <| show a + (-b) = b + (-b) by rw [← sub_eq_add_neg, h, add_neg_self]

theorem pow_succ'' [Monoid M] : ∀ (n : ℕ) (a : M), a ^ n.succ = a * a ^ n :=
Monoid.npow_succ'

/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  zero_mul : ∀ a : M₀, 0 * a = 0
  mul_zero : ∀ a : M₀, a * 0 = 0

export MulZeroClass (zero_mul mul_zero)
attribute [simp] zero_mul mul_zero

/-- Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `G₀`. -/
class NoZeroDivisors (M₀ : Type _) [Mul M₀] [Zero M₀] : Prop where
  /-- For all `a` and `b` of `G₀`, `a * b = 0` implies `a = 0` or `b = 0`. -/
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0

export NoZeroDivisors (eq_zero_or_eq_zero_of_mul_eq_zero)
/-- A type `S₀` is a "semigroup with zero” if it is a semigroup with zero element, and `0` is left
and right absorbing. -/
class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀

/-- A typeclass for non-associative monoids with zero elements. -/
class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀

/-- A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀

/-- A type `M` is a `CancelMonoidWithZero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
class CancelMonoidWithZero (M₀ : Type _) extends MonoidWithZero M₀ where
  /-- Left multiplication by a non-zero element is injective. -/
  protected mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c
  /-- Right multiplication by a non-zero element is injective. -/
  protected mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  CancelMonoidWithZero.mul_left_cancel_of_ne_zero ha h

theorem mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
  CancelMonoidWithZero.mul_right_cancel_of_ne_zero hb h

theorem mul_right_injective₀ (ha : a ≠ 0) : Function.Injective ((· * ·) a) :=
  fun _ _ => mul_left_cancel₀ ha

theorem mul_left_injective₀ (hb : b ≠ 0) : Function.Injective fun a => a * b :=
  fun _ _ => mul_right_cancel₀ hb

end CancelMonoidWithZero

/-- A type `M` is a commutative “monoid with zero” if it is a commutative monoid with zero
element, and `0` is left and right absorbing. -/
class CommMonoidWithZero (M₀ : Type _) extends CommMonoid M₀, MonoidWithZero M₀

/-- A type `M` is a `CancelCommMonoidWithZero` if it is a commutative monoid with zero element,
 `0` is left and right absorbing,
  and left/right multiplication by a non-zero element is injective. -/
class CancelCommMonoidWithZero (M₀ : Type _) extends CommMonoidWithZero M₀, CancelMonoidWithZero M₀

/-- A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory.-/
class GroupWithZero (G₀ : Type u) extends DivInvMonoid G₀, MonoidWithZero G₀ where
  /-- There are two distinct elements in a group with zero. -/
  exists_pair_ne : ∃ (x y : G₀), x ≠ y
  /-- The inverse of `0` in a group with zero is `0`. -/
  inv_zero : (0 : G₀)⁻¹ = 0
  /-- Every nonzero element of a group with zero is invertible. -/
  mul_inv_cancel (a : G₀) : a ≠ 0 → a * a⁻¹ = 1

export GroupWithZero (inv_zero mul_inv_cancel)
attribute [simp] inv_zero mul_inv_cancel

/-- A type `G₀` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
class CommGroupWithZero (G₀ : Type _) extends CommMonoidWithZero G₀, GroupWithZero G₀

/-! ### Additive monoids with one -/

class AddMonoidWithOne (R : Type u) extends AddMonoid R, One R where
  natCast : ℕ → R
  natCast_zero : natCast 0 = 0
  natCast_succ : ∀ n, natCast (n + 1) = natCast n + 1

@[coe]
def Nat.cast [AddMonoidWithOne R] : ℕ → R := AddMonoidWithOne.natCast

instance [AddMonoidWithOne R] : CoeTail ℕ R where coe := Nat.cast
instance [AddMonoidWithOne R] : CoeHTCT ℕ R where coe := Nat.cast

@[simp, norm_cast] theorem Nat.cast_zero [AddMonoidWithOne R] : ((0 : ℕ) : R) = 0 :=
  AddMonoidWithOne.natCast_zero
@[simp 500, norm_cast 500]
theorem Nat.cast_succ [AddMonoidWithOne R] : ((Nat.succ n : ℕ) : R) = (n : R) + 1 :=
  AddMonoidWithOne.natCast_succ _
@[simp, norm_cast]
theorem Nat.cast_one [AddMonoidWithOne R] : ((1 : ℕ) : R) = 1 := by simp

@[simp, norm_cast] theorem Nat.cast_add [AddMonoidWithOne R] : ((m + n : ℕ) : R) = (m : R) + n := by
  induction n <;> simp_all [add_succ, add_assoc]

class Nat.AtLeastTwo (n : Nat) : Prop where
  prop : n ≥ 2
instance : Nat.AtLeastTwo (n + 2) where
  prop := Nat.succ_le_succ $ Nat.succ_le_succ $ Nat.zero_le _

@[nolint unusedArguments]
instance [AddMonoidWithOne R] [Nat.AtLeastTwo n] : OfNat R n where
  ofNat := n.cast

@[simp, norm_cast] theorem Nat.cast_ofNat [AddMonoidWithOne R] [Nat.AtLeastTwo n] :
  (Nat.cast (OfNat.ofNat n) : R) = OfNat.ofNat n := rfl

/-! ### Additive groups with one -/

class AddGroupWithOne (R : Type u) extends AddMonoidWithOne R, AddGroup R where
  intCast : ℤ → R
  intCast_ofNat : ∀ n : ℕ, intCast n = natCast n
  intCast_negSucc : ∀ n : ℕ, intCast (Int.negSucc n) = - natCast (n + 1)

namespace Int

@[coe] def cast [AddGroupWithOne R] : ℤ → R := AddGroupWithOne.intCast

instance [AddGroupWithOne R] : CoeTail ℤ R where coe := cast

@[simp high, nolint simpNF] -- this lemma competes with `Int.ofNat_eq_cast` to come later
theorem cast_ofNat [AddGroupWithOne R] : (cast (ofNat n) : R) = Nat.cast n :=
  AddGroupWithOne.intCast_ofNat _
#align int.cast_coe_nat Int.cast_ofNat

@[simp, norm_cast]
theorem cast_negSucc [AddGroupWithOne R] :
    (cast (negSucc n) : R) = (-(Nat.cast (n + 1)) : R) :=
  AddGroupWithOne.intCast_negSucc _
#align int.cast_neg_succ_of_nat Int.cast_negSucc

@[simp, norm_cast] theorem cast_zero [AddGroupWithOne R] : ((0 : ℤ) : R) = 0 := by
  erw [cast_ofNat, Nat.cast_zero]
@[simp, norm_cast] theorem cast_one [AddGroupWithOne R] : ((1 : ℤ) : R) = 1 := by
  erw [cast_ofNat, Nat.cast_one]

end Int
