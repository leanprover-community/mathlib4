/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Nontrivial
import Mathlib.Algebra.NeZero

#align_import algebra.group_with_zero.defs from "leanprover-community/mathlib"@"2f3994e1b117b1e1da49bcfb67334f33460c3ce4"

/-!
# Typeclasses for groups with an adjoined zero element

This file provides just the typeclass definitions, and the projection lemmas that expose their
members.

## Main definitions

* `GroupWithZero`
* `CommGroupWithZero`
-/


universe u

set_option autoImplicit true

-- We have to fix the universe of `G₀` here, since the default argument to
-- `GroupWithZero.div'` cannot contain a universe metavariable.
variable {G₀ : Type u} {M₀ M₀' G₀' : Type*}

-- Porting note:
-- This theorem was introduced during ad-hoc porting
-- and hopefully can be removed again after `Mathlib.Algebra.Ring.Basic` is fully ported.
theorem eq_of_sub_eq_zero' [AddGroup R] {a b : R} (h : a - b = 0) : a = b :=
  add_right_cancel <| show a + (-b) = b + (-b) by rw [← sub_eq_add_neg, h, add_neg_self]
                                                  -- 🎉 no goals

-- Porting note:
-- This theorem was introduced during ad-hoc porting
-- and hopefully can be removed again after `Mathlib.Algebra.Ring.Basic` is fully ported.
theorem pow_succ'' [Monoid M] : ∀ (n : ℕ) (a : M), a ^ n.succ = a * a ^ n :=
  Monoid.npow_succ

/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  /-- Zero is a left absorbing element for multiplication -/
  zero_mul : ∀ a : M₀, 0 * a = 0
  /-- Zero is a right absorbing element for multiplication -/
  mul_zero : ∀ a : M₀, a * 0 = 0
#align mul_zero_class MulZeroClass

/-- A mixin for left cancellative multiplication by nonzero elements. -/
class IsLeftCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  /-- Multiplication by a nonzero element is left cancellative. -/
  protected mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c
#align is_left_cancel_mul_zero IsLeftCancelMulZero

section IsLeftCancelMulZero

variable [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}

theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha h
#align mul_left_cancel₀ mul_left_cancel₀

theorem mul_right_injective₀ (ha : a ≠ 0) : Function.Injective ((· * ·) a) :=
  fun _ _ => mul_left_cancel₀ ha
#align mul_right_injective₀ mul_right_injective₀

end IsLeftCancelMulZero

/-- A mixin for right cancellative multiplication by nonzero elements. -/
class IsRightCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  /-- Multiplicatin by a nonzero element is right cancellative. -/
  protected mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c
#align is_right_cancel_mul_zero IsRightCancelMulZero

section IsRightCancelMulZero

variable [Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀] {a b c : M₀}

theorem mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
  IsRightCancelMulZero.mul_right_cancel_of_ne_zero hb h
#align mul_right_cancel₀ mul_right_cancel₀

theorem mul_left_injective₀ (hb : b ≠ 0) : Function.Injective fun a => a * b :=
  fun _ _ => mul_right_cancel₀ hb
#align mul_left_injective₀ mul_left_injective₀

end IsRightCancelMulZero

/-- A mixin for cancellative multiplication by nonzero elements. -/
class IsCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀]
  extends IsLeftCancelMulZero M₀, IsRightCancelMulZero M₀ : Prop
#align is_cancel_mul_zero IsCancelMulZero

export MulZeroClass (zero_mul mul_zero)
attribute [simp] zero_mul mul_zero
#align zero_mul MulZeroClass.zero_mul
#align mul_zero MulZeroClass.mul_zero

/-- Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `G₀`. -/
class NoZeroDivisors (M₀ : Type*) [Mul M₀] [Zero M₀] : Prop where
  /-- For all `a` and `b` of `G₀`, `a * b = 0` implies `a = 0` or `b = 0`. -/
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0
#align no_zero_divisors NoZeroDivisors

export NoZeroDivisors (eq_zero_or_eq_zero_of_mul_eq_zero)
/-- A type `S₀` is a "semigroup with zero” if it is a semigroup with zero element, and `0` is left
and right absorbing. -/
class SemigroupWithZero (S₀ : Type u) extends Semigroup S₀, MulZeroClass S₀
#align semigroup_with_zero SemigroupWithZero

/-- A typeclass for non-associative monoids with zero elements. -/
class MulZeroOneClass (M₀ : Type u) extends MulOneClass M₀, MulZeroClass M₀
#align mul_zero_one_class MulZeroOneClass

/-- A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
class MonoidWithZero (M₀ : Type u) extends Monoid M₀, MulZeroOneClass M₀, SemigroupWithZero M₀
#align monoid_with_zero MonoidWithZero

/-- A type `M` is a `CancelMonoidWithZero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
class CancelMonoidWithZero (M₀ : Type*) extends MonoidWithZero M₀, IsCancelMulZero M₀
#align cancel_monoid_with_zero CancelMonoidWithZero

/-- A type `M` is a commutative “monoid with zero” if it is a commutative monoid with zero
element, and `0` is left and right absorbing. -/
class CommMonoidWithZero (M₀ : Type*) extends CommMonoid M₀, MonoidWithZero M₀
#align comm_monoid_with_zero CommMonoidWithZero

section CommSemigroup

variable [CommSemigroup M₀] [Zero M₀]

lemma IsLeftCancelMulZero.to_isRightCancelMulZero [IsLeftCancelMulZero M₀] :
    IsRightCancelMulZero M₀ :=
{ mul_right_cancel_of_ne_zero :=
    fun hb h => mul_left_cancel₀ hb <| (mul_comm _ _).trans (h.trans (mul_comm _ _)) }
#align is_left_cancel_mul_zero.to_is_right_cancel_mul_zero IsLeftCancelMulZero.to_isRightCancelMulZero

lemma IsRightCancelMulZero.to_isLeftCancelMulZero [IsRightCancelMulZero M₀] :
    IsLeftCancelMulZero M₀ :=
{ mul_left_cancel_of_ne_zero :=
    fun hb h => mul_right_cancel₀ hb <| (mul_comm _ _).trans (h.trans (mul_comm _ _)) }
#align is_right_cancel_mul_zero.to_is_left_cancel_mul_zero IsRightCancelMulZero.to_isLeftCancelMulZero

lemma IsLeftCancelMulZero.to_isCancelMulZero [IsLeftCancelMulZero M₀] :
    IsCancelMulZero M₀ :=
{ IsLeftCancelMulZero.to_isRightCancelMulZero with }
#align is_left_cancel_mul_zero.to_is_cancel_mul_zero IsLeftCancelMulZero.to_isCancelMulZero

lemma IsRightCancelMulZero.to_isCancelMulZero [IsRightCancelMulZero M₀] :
    IsCancelMulZero M₀ :=
{ IsRightCancelMulZero.to_isLeftCancelMulZero with }
#align is_right_cancel_mul_zero.to_is_cancel_mul_zero IsRightCancelMulZero.to_isCancelMulZero

end CommSemigroup

/-- A type `M` is a `CancelCommMonoidWithZero` if it is a commutative monoid with zero element,
 `0` is left and right absorbing,
  and left/right multiplication by a non-zero element is injective. -/
class CancelCommMonoidWithZero (M₀ : Type*) extends CommMonoidWithZero M₀, IsLeftCancelMulZero M₀
#align cancel_comm_monoid_with_zero CancelCommMonoidWithZero

-- See note [lower cancel priority]
attribute [instance 75] CancelCommMonoidWithZero.toCommMonoidWithZero

instance (priority := 100) CancelCommMonoidWithZero.toCancelMonoidWithZero
    [CancelCommMonoidWithZero M₀] : CancelMonoidWithZero M₀ :=
{ IsLeftCancelMulZero.to_isCancelMulZero (M₀ := M₀) with }

/-- A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory.-/
class GroupWithZero (G₀ : Type u) extends MonoidWithZero G₀, DivInvMonoid G₀, Nontrivial G₀ where
  /-- The inverse of `0` in a group with zero is `0`. -/
  inv_zero : (0 : G₀)⁻¹ = 0
  /-- Every nonzero element of a group with zero is invertible. -/
  mul_inv_cancel (a : G₀) : a ≠ 0 → a * a⁻¹ = 1
#align group_with_zero GroupWithZero

export GroupWithZero (inv_zero)
attribute [simp] inv_zero

@[simp] lemma mul_inv_cancel [GroupWithZero G₀] {a : G₀} (h : a ≠ 0) : a * a⁻¹ = 1 :=
  GroupWithZero.mul_inv_cancel a h
#align mul_inv_cancel mul_inv_cancel

/-- A type `G₀` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
class CommGroupWithZero (G₀ : Type*) extends CommMonoidWithZero G₀, GroupWithZero G₀
#align comm_group_with_zero CommGroupWithZero

section NeZero

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

variable (M₀)

/-- In a nontrivial monoid with zero, zero and one are different. -/
instance NeZero.one : NeZero (1 : M₀) := ⟨by
  intro h
  -- ⊢ False
  rcases exists_pair_ne M₀ with ⟨x, y, hx⟩
  -- ⊢ False
  apply hx
  -- ⊢ x = y
  calc
    x = 1 * x := by rw [one_mul]
    _ = 0 := by rw [h, zero_mul]
    _ = 1 * y := by rw [h, zero_mul]
    _ = y := by rw [one_mul]⟩
#align ne_zero.one NeZero.one

variable {M₀}

/-- Pullback a `Nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
theorem pullback_nonzero [Zero M₀'] [One M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    Nontrivial M₀' :=
  ⟨⟨0, 1, mt (congr_arg f) <| by
    rw [zero, one]
    -- ⊢ ¬0 = 1
    exact zero_ne_one⟩⟩
    -- 🎉 no goals
#align pullback_nonzero pullback_nonzero

end NeZero

section MulZeroClass

variable [MulZeroClass M₀]

theorem mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) : a * b = 0 := h.symm ▸ zero_mul b
#align mul_eq_zero_of_left mul_eq_zero_of_left

theorem mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0) : a * b = 0 := h.symm ▸ mul_zero a
#align mul_eq_zero_of_right mul_eq_zero_of_right

variable [NoZeroDivisors M₀] {a b : M₀}

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero,
    fun o => o.elim (fun h => mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩
#align mul_eq_zero mul_eq_zero

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 := by rw [eq_comm, mul_eq_zero]
                                                      -- 🎉 no goals
#align zero_eq_mul zero_eq_mul

/-- If `α` has no zero divisors, then the product of two elements is nonzero iff both of them
are nonzero. -/
theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := mul_eq_zero.not.trans not_or
#align mul_ne_zero_iff mul_ne_zero_iff

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero iff so is
`b * a`. -/
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
  mul_eq_zero.trans <| or_comm.trans mul_eq_zero.symm
#align mul_eq_zero_comm mul_eq_zero_comm

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero iff so is
`b * a`. -/
theorem mul_ne_zero_comm : a * b ≠ 0 ↔ b * a ≠ 0 := mul_eq_zero_comm.not
#align mul_ne_zero_comm mul_ne_zero_comm

theorem mul_self_eq_zero : a * a = 0 ↔ a = 0 := by simp
                                                   -- 🎉 no goals
#align mul_self_eq_zero mul_self_eq_zero

theorem zero_eq_mul_self : 0 = a * a ↔ a = 0 := by simp
                                                   -- 🎉 no goals
#align zero_eq_mul_self zero_eq_mul_self

theorem mul_self_ne_zero : a * a ≠ 0 ↔ a ≠ 0 := mul_self_eq_zero.not
#align mul_self_ne_zero mul_self_ne_zero

theorem zero_ne_mul_self : 0 ≠ a * a ↔ a ≠ 0 := zero_eq_mul_self.not
#align zero_ne_mul_self zero_ne_mul_self

end MulZeroClass
