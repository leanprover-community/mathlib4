/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Spread

/-!
# Lifting algebraic data classes along injective/surjective maps

This file provides definitions that are meant to deal with
situations such as the following:

Suppose that `G` is a group, and `H` is a type endowed with
`One H`, `Mul H`, and `Inv H`.
Suppose furthermore, that `f : G → H` is a surjective map
that respects the multiplication, and the unit elements.
Then `H` satisfies the group axioms.

The relevant definition in this case is `Function.Surjective.group`.
Dually, there is also `Function.Injective.group`.
And there are versions for (additive) (commutative) semigroups/monoids.

Note that the `nsmul` and `zsmul` hypotheses in the declarations in this file are declared as
`∀ x n, f (n • x) = n • f x`, with the binders in a slightly unnatural order, as they are
`to_additive`ized from the versions for `^`.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace Function

/-!
### Injective
-/

assert_not_exists MonoidWithZero DenselyOrdered AddMonoidWithOne

namespace Injective

variable {M₁ : Type*} {M₂ : Type*} [Mul M₁]

/-- A type endowed with `*` is a semigroup, if it admits an injective map that preserves `*` to
a semigroup. See note [reducible non-instances]. -/
@[to_additive /-- A type endowed with `+` is an additive semigroup, if it admits an
injective map that preserves `+` to an additive semigroup. -/]
protected abbrev semigroup [Semigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : Semigroup M₁ where
  mul_assoc := fun x y z => hf <| by rw [mul, mul, mul, mul, mul_assoc]

/-- A type endowed with `*` is a commutative magma, if it admits a surjective map that preserves
`*` from a commutative magma. -/
@[to_additive -- See note [reducible non-instances]
/-- A type endowed with `+` is an additive commutative semigroup, if it admits
a surjective map that preserves `+` from an additive commutative semigroup. -/]
protected abbrev commMagma [CommMagma M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommMagma M₁ where
  mul_comm x y := hf <| by rw [mul, mul, mul_comm]

/-- A type endowed with `*` is a commutative semigroup, if it admits an injective map that
preserves `*` to a commutative semigroup.  See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `+` is an additive commutative semigroup,if it admits
an injective map that preserves `+` to an additive commutative semigroup. -/]
protected abbrev commSemigroup [CommSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommSemigroup M₁ where
  toSemigroup := hf.semigroup f mul
  __ := hf.commMagma f mul

/-- A type has left-cancellative multiplication, if it admits an injective map that
preserves `*` to another type with left-cancellative multiplication. -/
@[to_additive /-- A type has left-cancellative addition, if it admits an injective map that
preserves `+` to another type with left-cancellative addition. -/]
protected theorem isLeftCancelMul [Mul M₂] [IsLeftCancelMul M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : IsLeftCancelMul M₁ where
  mul_left_cancel x y z H := hf <| mul_left_cancel <| by simpa only [mul] using congrArg f H

/-- A type has right-cancellative multiplication, if it admits an injective map that
preserves `*` to another type with right-cancellative multiplication. -/
@[to_additive /-- A type has right-cancellative addition, if it admits an injective map that
preserves `+` to another type with right-cancellative addition. -/]
protected theorem isRightCancelMul [Mul M₂] [IsRightCancelMul M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : IsRightCancelMul M₁ where
  mul_right_cancel x y z H := hf <| mul_right_cancel <| by simpa only [mul] using congrArg f H

/-- A type has cancellative multiplication, if it admits an injective map that
preserves `*` to another type with cancellative multiplication. -/
@[to_additive /-- A type has cancellative addition, if it admits an injective map that
preserves `+` to another type with cancellative addition. -/]
protected theorem isCancelMul [Mul M₂] [IsCancelMul M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : IsCancelMul M₁ where
  __ := hf.isLeftCancelMul f mul
  __ := hf.isRightCancelMul f mul

/-- A type endowed with `*` is a left cancel semigroup, if it admits an injective map that
preserves `*` to a left cancel semigroup.  See note [reducible non-instances]. -/
@[to_additive /-- A type endowed with `+` is an additive left cancel semigroup, if it admits an
injective map that preserves `+` to an additive left cancel semigroup. -/]
protected abbrev leftCancelSemigroup [LeftCancelSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftCancelSemigroup M₁ :=
  { hf.semigroup f mul, hf.isLeftCancelMul f mul with }

/-- A type endowed with `*` is a right cancel semigroup, if it admits an injective map that
preserves `*` to a right cancel semigroup.  See note [reducible non-instances]. -/
@[to_additive /-- A type endowed with `+` is an additive right
cancel semigroup, if it admits an injective map that preserves `+` to an additive right cancel
semigroup. -/]
protected abbrev rightCancelSemigroup [RightCancelSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightCancelSemigroup M₁ :=
  { hf.semigroup f mul, hf.isRightCancelMul f mul with }

variable [One M₁]

/-- A type endowed with `1` and `*` is a `MulOneClass`, if it admits an injective map that
preserves `1` and `*` to a `MulOneClass`.  See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an `AddZeroClass`, if it admits an
injective map that preserves `0` and `+` to an `AddZeroClass`. -/]
protected abbrev mulOneClass [MulOneClass M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : MulOneClass M₁ where
  one_mul := fun x => hf <| by rw [mul, one, one_mul]
  mul_one := fun x => hf <| by rw [mul, one, mul_one]

variable [Pow M₁ ℕ]

/-- A type endowed with `1` and `*` is a monoid, if it admits an injective map that preserves `1`
and `*` to a monoid.  See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an additive monoid, if it admits an
injective map that preserves `0` and `+` to an additive monoid. See note
[reducible non-instances]. -/]
protected abbrev monoid [Monoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : Monoid M₁ :=
  { hf.semigroup f mul, hf.mulOneClass f one mul with
    npow := fun n x => x ^ n,
    npow_zero := fun x => hf <| by rw [npow, one, pow_zero],
    npow_succ := fun n x => hf <| by rw [npow, pow_succ, mul, npow] }

/-- A type endowed with `1` and `*` is a left cancel monoid, if it admits an injective map that
preserves `1` and `*` to a left cancel monoid. See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an additive left cancel monoid, if it
admits an injective map that preserves `0` and `+` to an additive left cancel monoid. -/]
protected abbrev leftCancelMonoid [LeftCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : LeftCancelMonoid M₁ :=
  { hf.monoid f one mul npow, hf.leftCancelSemigroup f mul with }

/-- A type endowed with `1` and `*` is a right cancel monoid, if it admits an injective map that
preserves `1` and `*` to a right cancel monoid. See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an additive left cancel monoid,if it
admits an injective map that preserves `0` and `+` to an additive left cancel monoid. -/]
protected abbrev rightCancelMonoid [RightCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : RightCancelMonoid M₁ :=
  { hf.monoid f one mul npow, hf.rightCancelSemigroup f mul with }

/-- A type endowed with `1` and `*` is a cancel monoid, if it admits an injective map that preserves
`1` and `*` to a cancel monoid. See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an additive left cancel monoid,if it
admits an injective map that preserves `0` and `+` to an additive left cancel monoid. -/]
protected abbrev cancelMonoid [CancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CancelMonoid M₁ :=
  { hf.leftCancelMonoid f one mul npow, hf.rightCancelMonoid f one mul npow with }

/-- A type endowed with `1` and `*` is a commutative monoid, if it admits an injective map that
preserves `1` and `*` to a commutative monoid.  See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an additive commutative monoid, if it
admits an injective map that preserves `0` and `+` to an additive commutative monoid. -/]
protected abbrev commMonoid [CommMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoid M₁ :=
  { hf.monoid f one mul npow, hf.commSemigroup f mul with }

/-- A type endowed with `1` and `*` is a cancel commutative monoid if it admits an injective map
that preserves `1` and `*` to a cancel commutative monoid. See note [reducible non-instances]. -/
@[to_additive /-- A type endowed with `0` and `+` is an additive cancel commutative monoid if it
admits an injective map that preserves `0` and `+` to an additive cancel commutative monoid. -/]
protected abbrev cancelCommMonoid [CancelCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CancelCommMonoid M₁ :=
  { hf.commMonoid f one mul npow, hf.leftCancelSemigroup f mul with }

/-- A type has an involutive inversion if it admits a surjective map that preserves `⁻¹` to a type
which has an involutive inversion. See note [reducible non-instances] -/
@[to_additive
/-- A type has an involutive negation if it admits a surjective map that
preserves `-` to a type which has an involutive negation. -/]
protected abbrev involutiveInv {M₁ : Type*} [Inv M₁] [InvolutiveInv M₂] (f : M₁ → M₂)
    (hf : Injective f) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) : InvolutiveInv M₁ where
  inv_inv x := hf <| by rw [inv, inv, inv_inv]

variable [Inv M₁]

/-- A type endowed with `1` and `⁻¹` is a `InvOneClass`, if it admits an injective map that
preserves `1` and `⁻¹` to a `InvOneClass`.  See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and unary `-` is an `NegZeroClass`, if it admits an
injective map that preserves `0` and unary `-` to an `NegZeroClass`. -/]
protected abbrev invOneClass [InvOneClass M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) : InvOneClass M₁ where
  inv_one := hf <| by rw [inv, one, inv_one]

variable [Div M₁] [Pow M₁ ℤ]

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `DivInvMonoid` if it admits an injective map
that preserves `1`, `*`, `⁻¹`, and `/` to a `DivInvMonoid`. See note [reducible non-instances]. -/
@[to_additive subNegMonoid
/-- A type endowed with `0`, `+`, unary `-`, and binary `-` is a
`SubNegMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`, and binary `-` to
a `SubNegMonoid`. This version takes custom `nsmul` and `zsmul` as `[SMul ℕ M₁]` and `[SMul ℤ M₁]`
arguments. -/]
protected abbrev divInvMonoid [DivInvMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivInvMonoid M₁ :=
  { hf.monoid f one mul npow with
    zpow := fun n x => x ^ n,
    zpow_zero' := fun x => hf <| by rw [zpow, zpow_zero, one],
    zpow_succ' := fun n x => hf <| by rw [zpow, mul, zpow_natCast, pow_succ, zpow, zpow_natCast],
    zpow_neg' := fun n x => hf <| by rw [zpow, zpow_negSucc, inv, zpow, zpow_natCast],
    div_eq_mul_inv := fun x y => hf <| by rw [div, mul, inv, div_eq_mul_inv] }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `DivInvOneMonoid` if it admits an injective
map that preserves `1`, `*`, `⁻¹`, and `/` to a `DivInvOneMonoid`. See note
[reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0`, `+`, unary `-`, and binary `-` is a
`SubNegZeroMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`, and binary
`-` to a `SubNegZeroMonoid`. This version takes custom `nsmul` and `zsmul` as `[SMul ℕ M₁]` and
`[SMul ℤ M₁]` arguments. -/]
protected abbrev divInvOneMonoid [DivInvOneMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivInvOneMonoid M₁ :=
  { hf.divInvMonoid f one mul inv div npow zpow, hf.invOneClass f one inv with }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `DivisionMonoid` if it admits an injective map
that preserves `1`, `*`, `⁻¹`, and `/` to a `DivisionMonoid`. See note [reducible non-instances] -/
@[to_additive
/-- A type endowed with `0`, `+`, unary `-`, and binary `-`
is a `SubtractionMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`, and
binary `-` to a `SubtractionMonoid`. This version takes custom `nsmul` and `zsmul` as `[SMul ℕ M₁]`
and `[SMul ℤ M₁]` arguments. -/]
protected abbrev divisionMonoid [DivisionMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivisionMonoid M₁ :=
  { hf.divInvMonoid f one mul inv div npow zpow, hf.involutiveInv f inv with
    mul_inv_rev := fun x y => hf <| by rw [inv, mul, mul_inv_rev, mul, inv, inv],
    inv_eq_of_mul := fun x y h => hf <| by
      rw [inv, inv_eq_of_mul_eq_one_right (by rw [← mul, h, one])] }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `DivisionCommMonoid` if it admits an
injective map that preserves `1`, `*`, `⁻¹`, and `/` to a `DivisionCommMonoid`.
See note [reducible non-instances]. -/
@[to_additive subtractionCommMonoid
/-- A type endowed with `0`, `+`, unary `-`, and binary
`-` is a `SubtractionCommMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`,
and binary `-` to a `SubtractionCommMonoid`. This version takes custom `nsmul` and `zsmul` as
`[SMul ℕ M₁]` and `[SMul ℤ M₁]` arguments. -/]
protected abbrev divisionCommMonoid [DivisionCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivisionCommMonoid M₁ :=
  { hf.divisionMonoid f one mul inv div npow zpow, hf.commSemigroup f mul with }

/-- A type endowed with `1`, `*` and `⁻¹` is a group, if it admits an injective map that preserves
`1`, `*` and `⁻¹` to a group. See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an additive group, if it admits an
injective map that preserves `0` and `+` to an additive group. -/]
protected abbrev group [Group M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : Group M₁ :=
  { hf.divInvMonoid f one mul inv div npow zpow with
    inv_mul_cancel := fun x => hf <| by rw [mul, inv, inv_mul_cancel, one] }


/-- A type endowed with `1`, `*` and `⁻¹` is a commutative group, if it admits an injective map that
preserves `1`, `*` and `⁻¹` to a commutative group. See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an additive commutative group, if it
admits an injective map that preserves `0` and `+` to an additive commutative group. -/]
protected abbrev commGroup [CommGroup M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroup M₁ :=
  { hf.group f one mul inv div npow zpow, hf.commMonoid f one mul npow with }

end Injective

/-!
### Surjective
-/


namespace Surjective

variable {M₁ : Type*} {M₂ : Type*} [Mul M₂]

/-- A type endowed with `*` is a semigroup, if it admits a surjective map that preserves `*` from a
semigroup. See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `+` is an additive semigroup, if it admits a
surjective map that preserves `+` from an additive semigroup. -/]
protected abbrev semigroup [Semigroup M₁] (f : M₁ → M₂) (hf : Surjective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : Semigroup M₂ where
  mul_assoc := hf.forall₃.2 fun x y z => by simp only [← mul, mul_assoc]

/-- A type endowed with `*` is a commutative semigroup, if it admits a surjective map that preserves
`*` from a commutative semigroup. See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `+` is an additive commutative semigroup, if it admits
a surjective map that preserves `+` from an additive commutative semigroup. -/]
protected abbrev commMagma [CommMagma M₁] (f : M₁ → M₂) (hf : Surjective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommMagma M₂ where
  mul_comm := hf.forall₂.2 fun x y => by rw [← mul, ← mul, mul_comm]

/-- A type endowed with `*` is a commutative semigroup, if it admits a surjective map that preserves
`*` from a commutative semigroup. See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `+` is an additive commutative semigroup, if it admits
a surjective map that preserves `+` from an additive commutative semigroup. -/]
protected abbrev commSemigroup [CommSemigroup M₁] (f : M₁ → M₂) (hf : Surjective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommSemigroup M₂ where
  toSemigroup := hf.semigroup f mul
  __ := hf.commMagma f mul

variable [One M₂]

/-- A type endowed with `1` and `*` is a `MulOneClass`, if it admits a surjective map that preserves
`1` and `*` from a `MulOneClass`. See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an `AddZeroClass`, if it admits a
surjective map that preserves `0` and `+` to an `AddZeroClass`. -/]
protected abbrev mulOneClass [MulOneClass M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : MulOneClass M₂ where
  one_mul := hf.forall.2 fun x => by rw [← one, ← mul, one_mul]
  mul_one := hf.forall.2 fun x => by rw [← one, ← mul, mul_one]

variable [Pow M₂ ℕ]

/-- A type endowed with `1` and `*` is a monoid, if it admits a surjective map that preserves `1`
and `*` to a monoid. See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an additive monoid, if it admits a
surjective map that preserves `0` and `+` to an additive monoid. This version takes a custom `nsmul`
as a `[SMul ℕ M₂]` argument. -/]
protected abbrev monoid [Monoid M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : Monoid M₂ :=
  { hf.semigroup f mul, hf.mulOneClass f one mul with
    npow := fun n x => x ^ n,
    npow_zero := hf.forall.2 fun x => by rw [← npow, pow_zero, ← one],
    npow_succ := fun n => hf.forall.2 fun x => by
      rw [← npow, pow_succ, ← npow, ← mul] }


/-- A type endowed with `1` and `*` is a commutative monoid, if it admits a surjective map that
preserves `1` and `*` from a commutative monoid. See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an additive commutative monoid, if it
admits a surjective map that preserves `0` and `+` to an additive commutative monoid. -/]
protected abbrev commMonoid [CommMonoid M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoid M₂ :=
  { hf.monoid f one mul npow, hf.commSemigroup f mul with }

/-- A type has an involutive inversion if it admits a surjective map that preserves `⁻¹` to a type
which has an involutive inversion. See note [reducible non-instances] -/
@[to_additive
/-- A type has an involutive negation if it admits a surjective map that
preserves `-` to a type which has an involutive negation. -/]
protected abbrev involutiveInv {M₂ : Type*} [Inv M₂] [InvolutiveInv M₁] (f : M₁ → M₂)
    (hf : Surjective f) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) : InvolutiveInv M₂ where
  inv_inv := hf.forall.2 fun x => by rw [← inv, ← inv, inv_inv]

variable [Inv M₂] [Div M₂] [Pow M₂ ℤ]

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `DivInvMonoid` if it admits a surjective map
that preserves `1`, `*`, `⁻¹`, and `/` to a `DivInvMonoid`. See note [reducible non-instances]. -/
@[to_additive subNegMonoid
/-- A type endowed with `0`, `+`, unary `-`, and binary `-` is a
`SubNegMonoid` if it admits a surjective map that preserves `0`, `+`, unary `-`, and binary `-` to
a `SubNegMonoid`. -/]
protected abbrev divInvMonoid [DivInvMonoid M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivInvMonoid M₂ :=
  { hf.monoid f one mul npow with
    zpow := fun n x => x ^ n,
    zpow_zero' := hf.forall.2 fun x => by rw [← zpow, zpow_zero, ← one],
    zpow_succ' := fun n => hf.forall.2 fun x => by
      rw [← zpow, ← zpow, zpow_natCast, zpow_natCast, pow_succ, ← mul],
    zpow_neg' := fun n => hf.forall.2 fun x => by
      rw [← zpow, ← zpow, zpow_negSucc, zpow_natCast, inv],
    div_eq_mul_inv := hf.forall₂.2 fun x y => by rw [← inv, ← mul, ← div, div_eq_mul_inv] }

/-- A type endowed with `1`, `*` and `⁻¹` is a group, if it admits a surjective map that preserves
`1`, `*` and `⁻¹` to a group. See note [reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an additive group, if it admits a
surjective map that preserves `0` and `+` to an additive group. -/]
protected abbrev group [Group M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : Group M₂ :=
  { hf.divInvMonoid f one mul inv div npow zpow with
    inv_mul_cancel := hf.forall.2 fun x => by rw [← inv, ← mul, inv_mul_cancel, one] }

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a commutative group, if it admits a surjective
map that preserves `1`, `*`, `⁻¹`, and `/` from a commutative group. See note
[reducible non-instances]. -/
@[to_additive
/-- A type endowed with `0` and `+` is an additive commutative group, if it
admits a surjective map that preserves `0` and `+` to an additive commutative group. -/]
protected abbrev commGroup [CommGroup M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroup M₂ :=
  { hf.group f one mul inv div npow zpow, hf.commMonoid f one mul npow with }

end Surjective

end Function
