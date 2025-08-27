/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Tactic.SplitIfs
import Mathlib.Logic.Basic

/-!
# Typeclasses for groups with an adjoined zero element

This file provides just the typeclass definitions, and the projection lemmas that expose their
members.

## Main definitions

* `GroupWithZero`
* `CommGroupWithZero`
-/

assert_not_exists DenselyOrdered Ring

universe u

-- We have to fix the universe of `G₀` here, since the default argument to
-- `GroupWithZero.div'` cannot contain a universe metavariable.
variable {G₀ : Type u} {M₀ : Type*}

/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
class MulZeroClass (M₀ : Type u) extends Mul M₀, Zero M₀ where
  /-- Zero is a left absorbing element for multiplication -/
  zero_mul : ∀ a : M₀, 0 * a = 0
  /-- Zero is a right absorbing element for multiplication -/
  mul_zero : ∀ a : M₀, a * 0 = 0

/-- A mixin for left cancellative multiplication by nonzero elements. -/
@[mk_iff] class IsLeftCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  /-- Multiplication by a nonzero element is left cancellative. -/
  protected mul_left_cancel_of_ne_zero : ∀ {a : M₀}, a ≠ 0 → IsLeftRegular a

section IsLeftCancelMulZero

variable [Mul M₀] [Zero M₀] [IsLeftCancelMulZero M₀] {a b c : M₀}

theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  IsLeftCancelMulZero.mul_left_cancel_of_ne_zero ha h

theorem mul_right_injective₀ (ha : a ≠ 0) : Function.Injective (a * ·) :=
  fun _ _ => mul_left_cancel₀ ha

end IsLeftCancelMulZero

/-- A mixin for right cancellative multiplication by nonzero elements. -/
@[mk_iff] class IsRightCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop where
  /-- Multiplication by a nonzero element is right cancellative. -/
  protected mul_right_cancel_of_ne_zero : ∀ {a : M₀}, a ≠ 0 → IsRightRegular a

section IsRightCancelMulZero

variable [Mul M₀] [Zero M₀] [IsRightCancelMulZero M₀] {a b c : M₀}

theorem mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
  IsRightCancelMulZero.mul_right_cancel_of_ne_zero hb h

theorem mul_left_injective₀ (hb : b ≠ 0) : Function.Injective fun a => a * b :=
  fun _ _ => mul_right_cancel₀ hb

end IsRightCancelMulZero

/-- A mixin for cancellative multiplication by nonzero elements. -/
@[mk_iff] class IsCancelMulZero (M₀ : Type u) [Mul M₀] [Zero M₀] : Prop
  extends IsLeftCancelMulZero M₀, IsRightCancelMulZero M₀

export MulZeroClass (zero_mul mul_zero)
attribute [simp] zero_mul mul_zero

theorem isCancelMulZero_iff_forall_isRegular {M₀} [Mul M₀] [Zero M₀] :
    IsCancelMulZero M₀ ↔ ∀ {a : M₀}, a ≠ 0 → IsRegular a := by
  simp only [isCancelMulZero_iff, isLeftCancelMulZero_iff, isRightCancelMulZero_iff, ← forall_and]
  exact forall₂_congr fun _ _ ↦ isRegular_iff.symm

/-- Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `M₀`. It is weaker than `IsCancelMulZero` in general,
but equivalent to it if `M₀` is a (not necessarily unital or associative) ring. -/
@[mk_iff] class NoZeroDivisors (M₀ : Type*) [Mul M₀] [Zero M₀] : Prop where
  /-- For all `a` and `b` of `M₀`, `a * b = 0` implies `a = 0` or `b = 0`. -/
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

section MonoidWithZero

variable [MonoidWithZero M₀]

/-- If `x` is multiplicative with respect to `f`, then so is any `x^n`. -/
theorem pow_mul_apply_eq_pow_mul {M : Type*} [Monoid M] (f : M₀ → M) {x : M₀}
    (hx : ∀ y : M₀, f (x * y) = f x * f y) (n : ℕ) :
    ∀ (y : M₀), f (x ^ n * y) = f x ^ n * f y := by
  induction n with
  | zero => intro y; rw [pow_zero, pow_zero, one_mul, one_mul]
  | succ n hn => intro y; rw [pow_succ', pow_succ', mul_assoc, mul_assoc, hx, hn]

end MonoidWithZero

/-- A type `M` is a `CancelMonoidWithZero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
class CancelMonoidWithZero (M₀ : Type*) extends MonoidWithZero M₀, IsCancelMulZero M₀

/-- A type `M` is a commutative “monoid with zero” if it is a commutative monoid with zero
element, and `0` is left and right absorbing. -/
class CommMonoidWithZero (M₀ : Type*) extends CommMonoid M₀, MonoidWithZero M₀

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

theorem mul_left_inj' (hc : c ≠ 0) : a * c = b * c ↔ a = b :=
  (mul_left_injective₀ hc).eq_iff

theorem mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  (mul_right_injective₀ ha).eq_iff

end CancelMonoidWithZero

section CommSemigroup

variable [CommSemigroup M₀] [Zero M₀]

lemma IsLeftCancelMulZero.to_isRightCancelMulZero [IsLeftCancelMulZero M₀] :
    IsRightCancelMulZero M₀ :=
{ mul_right_cancel_of_ne_zero :=
    fun hb _ _ h => mul_left_cancel₀ hb <| (mul_comm _ _).trans (h.trans (mul_comm _ _)) }

lemma IsRightCancelMulZero.to_isLeftCancelMulZero [IsRightCancelMulZero M₀] :
    IsLeftCancelMulZero M₀ :=
{ mul_left_cancel_of_ne_zero :=
    fun hb _ _ h => mul_right_cancel₀ hb <| (mul_comm _ _).trans (h.trans (mul_comm _ _)) }

lemma IsLeftCancelMulZero.to_isCancelMulZero [IsLeftCancelMulZero M₀] :
    IsCancelMulZero M₀ :=
{ IsLeftCancelMulZero.to_isRightCancelMulZero with }

lemma IsRightCancelMulZero.to_isCancelMulZero [IsRightCancelMulZero M₀] :
    IsCancelMulZero M₀ :=
{ IsRightCancelMulZero.to_isLeftCancelMulZero with }

end CommSemigroup

/-- A type `M` is a `CancelCommMonoidWithZero` if it is a commutative monoid with zero element,
`0` is left and right absorbing,
and left/right multiplication by a non-zero element is injective. -/
class CancelCommMonoidWithZero (M₀ : Type*) extends CommMonoidWithZero M₀, IsLeftCancelMulZero M₀

-- See note [lower cancel priority]
attribute [instance 75] CancelCommMonoidWithZero.toCommMonoidWithZero

instance (priority := 100) CancelCommMonoidWithZero.toCancelMonoidWithZero
    [CancelCommMonoidWithZero M₀] : CancelMonoidWithZero M₀ :=
{ IsLeftCancelMulZero.to_isCancelMulZero (M₀ := M₀) with }

/-- Prop-valued mixin for a monoid with zero to be equipped with a cancelling division.

The obvious use case is groups with zero, but this condition is also satisfied by `ℕ`, `ℤ` and, more
generally, any Euclidean domain. -/
class MulDivCancelClass (M₀ : Type*) [MonoidWithZero M₀] [Div M₀] : Prop where
  protected mul_div_cancel (a b : M₀) : b ≠ 0 → a * b / b = a

section MulDivCancelClass
variable [MonoidWithZero M₀] [Div M₀] [MulDivCancelClass M₀]

@[simp] lemma mul_div_cancel_right₀ (a : M₀) {b : M₀} (hb : b ≠ 0) : a * b / b = a :=
  MulDivCancelClass.mul_div_cancel _ _ hb

end MulDivCancelClass

section MulDivCancelClass
variable [CommMonoidWithZero M₀] [Div M₀] [MulDivCancelClass M₀]

@[simp] lemma mul_div_cancel_left₀ (b : M₀) {a : M₀} (ha : a ≠ 0) : a * b / a = b := by
  rw [mul_comm, mul_div_cancel_right₀ _ ha]

end MulDivCancelClass

/-- A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory. -/
class GroupWithZero (G₀ : Type u) extends MonoidWithZero G₀, DivInvMonoid G₀, Nontrivial G₀ where
  /-- The inverse of `0` in a group with zero is `0`. -/
  protected inv_zero : (0 : G₀)⁻¹ = 0
  /-- Every nonzero element of a group with zero is invertible. -/
  protected mul_inv_cancel (a : G₀) : a ≠ 0 → a * a⁻¹ = 1

section GroupWithZero
variable [GroupWithZero G₀] {a : G₀}

@[simp] lemma inv_zero : (0 : G₀)⁻¹ = 0 := GroupWithZero.inv_zero

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel`
lemma mul_inv_cancel₀ (h : a ≠ 0) : a * a⁻¹ = 1 := GroupWithZero.mul_inv_cancel a h

-- See note [lower instance priority]
instance (priority := 100) GroupWithZero.toMulDivCancelClass : MulDivCancelClass G₀ where
  mul_div_cancel a b hb := by rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ hb, mul_one]

end GroupWithZero

/-- A type `G₀` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
class CommGroupWithZero (G₀ : Type*) extends CommMonoidWithZero G₀, GroupWithZero G₀

section
variable [CancelMonoidWithZero M₀] {x : M₀}

lemma eq_zero_or_one_of_sq_eq_self (hx : x ^ 2 = x) : x = 0 ∨ x = 1 :=
  or_iff_not_imp_left.mpr (mul_left_injective₀ · <| by simpa [sq] using hx)

end

section GroupWithZero

variable [GroupWithZero G₀] {a b : G₀}

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_right`
theorem mul_inv_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by simp [h]

@[simp high] -- should take priority over `IsUnit.mul_inv_cancel_left`
theorem mul_inv_cancel_left₀ (h : a ≠ 0) (b : G₀) : a * (a⁻¹ * b) = b :=
  calc
    a * (a⁻¹ * b) = a * a⁻¹ * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]

end GroupWithZero

section MulZeroClass

variable [MulZeroClass M₀]

theorem mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) : a * b = 0 := h.symm ▸ zero_mul b

theorem mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0) : a * b = 0 := h.symm ▸ mul_zero a

lemma noZeroDivisors_iff_right_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → ∀ y, x * y = 0 → y = 0 := by
  simp only [noZeroDivisors_iff, or_iff_not_imp_left]
  exact ⟨fun h a ha b eq ↦ h eq ha, fun h a b eq ha ↦ h a ha b eq⟩

lemma noZeroDivisors_iff_left_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → ∀ y, y * x = 0 → y = 0 := by
  simp only [noZeroDivisors_iff, or_iff_not_imp_right]
  exact ⟨fun h b hb a eq ↦ h eq hb, fun h a b eq hb ↦ h b hb a eq⟩

lemma noZeroDivisors_iff_eq_zero_of_mul :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → (∀ y, x * y = 0 → y = 0) ∧ (∀ y, y * x = 0 → y = 0) := by
  simp only [forall_and, ← noZeroDivisors_iff_right_eq_zero_of_mul,
    ← noZeroDivisors_iff_left_eq_zero_of_mul, and_self]

variable [NoZeroDivisors M₀] {a b : M₀}

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero,
    fun o ↦ o.elim (fun h ↦ mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

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

theorem mul_eq_zero_iff_left (ha : a ≠ 0) : a * b = 0 ↔ b = 0 := by simp [ha]

theorem mul_eq_zero_iff_right (hb : b ≠ 0) : a * b = 0 ↔ a = 0 := by simp [hb]

theorem mul_ne_zero_iff_left (ha : a ≠ 0) : a * b ≠ 0 ↔ b ≠ 0 := by simp [ha]

theorem mul_ne_zero_iff_right (hb : b ≠ 0) : a * b ≠ 0 ↔ a ≠ 0 := by simp [hb]

end MulZeroClass
