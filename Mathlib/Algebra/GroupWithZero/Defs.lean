/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Nontrivial
import Mathlib.Algebra.NeZero

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

-- Porting note:
-- This theorem was introduced during ad-hoc porting
-- and hopefully can be removed again after `Mathlib.Algebra.Ring.Basic` is fully ported.
theorem eq_of_sub_eq_zero' [AddGroup R] {a b : R} (h : a - b = 0) : a = b :=
  add_right_cancel <| show a + (-b) = b + (-b) by rw [← sub_eq_add_neg, h, add_neg_self]

-- Porting note:
-- This theorem was introduced during ad-hoc porting
-- and hopefully can be removed again after `Mathlib.Algebra.Ring.Basic` is fully ported.
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

export MulZeroClass (zero_mul mul_zero)
attribute [simp] zero_mul mul_zero

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

/-- A type `M` is a `CancelMonoidWithZero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
class CancelMonoidWithZero (M₀ : Type u) extends MonoidWithZero M₀ where
  /-- Left multiplication by a non-zero element is injective. -/
  protected mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c
  /-- Right multiplication by a non-zero element is injective. -/
  protected mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

lemma mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
CancelMonoidWithZero.mul_left_cancel_of_ne_zero ha h

lemma mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
CancelMonoidWithZero.mul_right_cancel_of_ne_zero hb h

lemma mul_right_injective₀ (ha : a ≠ 0) : Function.Injective (a * ·) :=
λ _ _ => mul_left_cancel₀ ha

lemma mul_left_injective₀ (hb : b ≠ 0) : Function.Injective (· * b) :=
λ _ _ => mul_right_cancel₀ hb

end CancelMonoidWithZero

section NeZero

attribute [field_simps] two_ne_zero three_ne_zero four_ne_zero

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

variable (M₀)

/-- In a nontrivial monoid with zero, zero and one are different. -/
instance NeZero.one : NeZero (1 : M₀) := ⟨by
  intro h
  rcases exists_pair_ne M₀ with ⟨x, y, hx⟩
  apply hx
  calc
    x = 1 * x := by rw [one_mul]
    _ = 0 := by rw [h, zero_mul]
    _ = 1 * y := by rw [h, zero_mul]
    _ = y := by rw [one_mul]⟩
#align ne_zero.one NeZero.one

variable {M₀}

/-- Pullback a `nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
theorem pullback_nonzero [Zero M₀'] [One M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    Nontrivial M₀' :=
  ⟨⟨0, 1, mt (congr_arg f) <| by
    rw [zero, one]
    exact zero_ne_one⟩⟩

end NeZero

section MulZeroClass

variable [MulZeroClass M₀]

theorem mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) : a * b = 0 := h.symm ▸ zero_mul b

theorem mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0) : a * b = 0 := h.symm ▸ mul_zero a

variable [NoZeroDivisors M₀] {a b : M₀}

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero,
    fun o => o.elim (fun h => mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 := by rw [eq_comm, mul_eq_zero]

/-- If `α` has no zero divisors, then the product of two elements is nonzero iff both of them
are nonzero. -/
theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := mul_eq_zero.not.trans not_or

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero iff so is
`b * a`. -/
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
  mul_eq_zero.trans <| or_comm.trans mul_eq_zero.symm

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero iff so is
`b * a`. -/
theorem mul_ne_zero_comm : a * b ≠ 0 ↔ b * a ≠ 0 := mul_eq_zero_comm.not

theorem mul_self_eq_zero : a * a = 0 ↔ a = 0 := by simp

theorem zero_eq_mul_self : 0 = a * a ↔ a = 0 := by simp

theorem mul_self_ne_zero : a * a ≠ 0 ↔ a ≠ 0 := mul_self_eq_zero.not

theorem zero_ne_mul_self : 0 ≠ a * a ↔ a ≠ 0 := zero_eq_mul_self.not

end MulZeroClass
