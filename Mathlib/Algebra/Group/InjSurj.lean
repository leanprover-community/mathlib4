/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic.Spread

#align_import algebra.group.inj_surj from "leanprover-community/mathlib"@"d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce"

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

## Implementation note

The `nsmul` and `zsmul` assumptions on any tranfer definition for an algebraic structure involving
both addition and multiplication (eg `AddMonoidWithOne`) is `∀ n x, f (n • x) = n • f x`, which is
what we would expect.
However, we cannot do the same for transfer definitions built using `to_additive` (eg `AddMonoid`)
as we want the multiplicative versions to be `∀ x n, f (x ^ n) = f x ^ n`.
As a result, we must use `Function.swap` when using additivised transfer definitions in
non-additivised ones.
-/


namespace Function

/-!
### Injective
-/

assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

namespace Injective

variable {M₁ : Type*} {M₂ : Type*} [Mul M₁] [Add M₁]

/-- A type endowed with `+` is an additive semigroup, if it admits an
injective map that preserves `+` to an additive semigroup." -/
protected abbrev addSemigroup [AddSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (add : ∀ x y, f (x + y) = f x + f y) : AddSemigroup M₁ :=
  { ‹Add M₁› with add_assoc := fun x y z => hf <| by erw [add, add, add, add, add_assoc] }
#align function.injective.add_semigroup Function.Injective.addSemigroup

/-- A type endowed with `*` is a semigroup, if it admits an injective map that preserves `*` to
a semigroup. See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev semigroup [Semigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : Semigroup M₁ :=
  { ‹Mul M₁› with mul_assoc := fun x y z => hf <| by erw [mul, mul, mul, mul, mul_assoc] }
#align function.injective.semigroup Function.Injective.semigroup

/-- A type endowed with `+` is an additive commutative semigroup, if it admits
a surjective map that preserves `+` from an additive commutative semigroup. -/
protected abbrev addCommMagma [AddCommMagma M₂] (f : M₁ → M₂) (hf : Injective f)
    (add : ∀ x y, f (x + y) = f x + f y) : AddCommMagma M₁ where
  add_comm x y := hf <| by rw [add, add, add_comm]

/-- A type endowed with `*` is a commutative magma, if it admits a surjective map that preserves
`*` from a commutative magma.  See note [reducible non-instances] -/
@[to_additive existing]
protected abbrev commMagma [CommMagma M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommMagma M₁ where
  mul_comm x y := hf <| by rw [mul, mul, mul_comm]

/-- A type endowed with `+` is an additive commutative semigroup,if it admits
an injective map that preserves `+` to an additive commutative semigroup. -/
protected abbrev addCommSemigroup [AddCommSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x + y) = f x + f y) : AddCommSemigroup M₁ where
  toAddSemigroup := hf.addSemigroup f mul
  __ := hf.addCommMagma f mul
#align function.injective.add_comm_semigroup Function.Injective.addCommSemigroup

/-- A type endowed with `*` is a commutative semigroup, if it admits an injective map that
preserves `*` to a commutative semigroup.  See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev commSemigroup [CommSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommSemigroup M₁ where
  toSemigroup := hf.semigroup f mul
  __ := hf.commMagma f mul
#align function.injective.comm_semigroup Function.Injective.commSemigroup

/-- A type endowed with `+` is an additive left cancel
semigroup, if it admits an injective map that preserves `+` to an additive left cancel semigroup. -/
protected abbrev addLeftCancelSemigroup [AddLeftCancelSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (add : ∀ x y, f (x + y) = f x + f y) : AddLeftCancelSemigroup M₁ :=
  { hf.addSemigroup f add with
    add_left_cancel := fun x y z H => hf <| (add_right_inj (f x)).1 <| by erw [← add, ← add, H] }
#align function.injective.add_left_cancel_semigroup Function.Injective.addLeftCancelSemigroup

/-- A type endowed with `*` is a left cancel semigroup, if it admits an injective map that
preserves `*` to a left cancel semigroup.  See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev leftCancelSemigroup [LeftCancelSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftCancelSemigroup M₁ :=
  { hf.semigroup f mul with
    mul_left_cancel := fun x y z H => hf <| (mul_right_inj (f x)).1 <| by erw [← mul, ← mul, H] }
#align function.injective.left_cancel_semigroup Function.Injective.leftCancelSemigroup

/-- A type endowed with `+` is an additive right
cancel semigroup, if it admits an injective map that preserves `+` to an additive right cancel
semigroup. -/
protected abbrev addRightCancelSemigroup [AddRightCancelSemigroup M₂] (f : M₁ → M₂)
    (hf : Injective f)
    (add : ∀ x y, f (x + y) = f x + f y) : AddRightCancelSemigroup M₁ :=
  { hf.addSemigroup f add with
    add_right_cancel := fun x y z H => hf <| (add_left_inj (f y)).1 <| by erw [← add, ← add, H] }
#align function.injective.add_right_cancel_semigroup Function.Injective.addRightCancelSemigroup

/-- A type endowed with `*` is a right cancel semigroup, if it admits an injective map that
preserves `*` to a right cancel semigroup.  See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev rightCancelSemigroup [RightCancelSemigroup M₂] (f : M₁ → M₂) (hf : Injective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightCancelSemigroup M₁ :=
  { hf.semigroup f mul with
    mul_right_cancel := fun x y z H => hf <| (mul_left_inj (f y)).1 <| by erw [← mul, ← mul, H] }
#align function.injective.right_cancel_semigroup Function.Injective.rightCancelSemigroup

variable [One M₁] [Zero M₁]

/-- A type endowed with `0` and `+` is an `AddZeroClass`, if it admits an
injective map that preserves `0` and `+` to an `AddZeroClass`." -/
protected abbrev addZeroClass [AddZeroClass M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) : AddZeroClass M₁ :=
  { ‹Zero M₁›, ‹Add M₁› with
    zero_add := fun x => hf <| by erw [add, zero, zero_add],
    add_zero := fun x => hf <| by erw [add, zero, add_zero] }
#align function.injective.add_zero_class Function.Injective.addZeroClass

/-- A type endowed with `1` and `*` is a `MulOneClass`, if it admits an injective map that
preserves `1` and `*` to a `MulOneClass`.  See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev mulOneClass [MulOneClass M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : MulOneClass M₁ :=
  { ‹One M₁›, ‹Mul M₁› with
    one_mul := fun x => hf <| by erw [mul, one, one_mul],
    mul_one := fun x => hf <| by erw [mul, one, mul_one] }
#align function.injective.mul_one_class Function.Injective.mulOneClass

variable [Pow M₁ ℕ] [SMul ℕ M₁]

/-- A type endowed with `0` and `+` is an additive monoid, if it admits an
injective map that preserves `0` and `+` to an additive monoid. See note
[reducible non-instances]. -/
protected abbrev addMonoid [AddMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) :
    AddMonoid M₁ :=
  { hf.addZeroClass f zero add, hf.addSemigroup f add with
    nsmul := fun n x => n • x,
    nsmul_zero := fun x => hf <| by erw [nsmul, zero, zero_nsmul],
    nsmul_succ := fun n x => hf <| by erw [nsmul, succ_nsmul, add, nsmul] }
#align function.injective.add_monoid Function.Injective.addMonoid

/-- A type endowed with `1` and `*` is a monoid, if it admits an injective map that preserves `1`
and `*` to a monoid.  See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev monoid [Monoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : Monoid M₁ :=
  { hf.mulOneClass f one mul, hf.semigroup f mul with
    npow := fun n x => x ^ n,
    npow_zero := fun x => hf <| by erw [npow, one, pow_zero],
    npow_succ := fun n x => hf <| by erw [npow, pow_succ, mul, npow] }
#align function.injective.monoid Function.Injective.monoid

/-- A type endowed with `0`, `1` and `+` is an additive monoid with one,
if it admits an injective map that preserves `0`, `1` and `+` to an additive monoid with one.
See note [reducible non-instances]. -/
protected abbrev addMonoidWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul ℕ M₁] [NatCast M₁]
    [AddMonoidWithOne M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddMonoidWithOne M₁ :=
  { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := hf (by erw [natCast, Nat.cast_zero, zero]),
    natCast_succ := fun n => hf (by erw [natCast, Nat.cast_succ, add, one, natCast]), one := 1 }
#align function.injective.add_monoid_with_one Function.Injective.addMonoidWithOne

/-- A type endowed with `0` and `+` is an additive left cancel monoid, if it
admits an injective map that preserves `0` and `+` to an additive left cancel monoid." -/
protected abbrev addLeftCancelMonoid [AddLeftCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : AddLeftCancelMonoid M₁ :=
  { hf.addLeftCancelSemigroup f add, hf.addMonoid f zero add nsmul with }
#align function.injective.add_left_cancel_monoid Function.Injective.addLeftCancelMonoid

/-- A type endowed with `1` and `*` is a left cancel monoid, if it admits an injective map that
preserves `1` and `*` to a left cancel monoid. See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev leftCancelMonoid [LeftCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : LeftCancelMonoid M₁ :=
  { hf.leftCancelSemigroup f mul, hf.monoid f one mul npow with }
#align function.injective.left_cancel_monoid Function.Injective.leftCancelMonoid

/-- A type endowed with `0` and `+` is an additive left cancel monoid,if it
admits an injective map that preserves `0` and `+` to an additive left cancel monoid. -/
protected abbrev addRightCancelMonoid [AddRightCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : AddRightCancelMonoid M₁ :=
  { hf.addRightCancelSemigroup f add, hf.addMonoid f zero add nsmul with }
#align function.injective.add_right_cancel_monoid Function.Injective.addRightCancelMonoid

/-- A type endowed with `1` and `*` is a right cancel monoid, if it admits an injective map that
preserves `1` and `*` to a right cancel monoid. See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev rightCancelMonoid [RightCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : RightCancelMonoid M₁ :=
  { hf.rightCancelSemigroup f mul, hf.monoid f one mul npow with }
#align function.injective.right_cancel_monoid Function.Injective.rightCancelMonoid

/-- A type endowed with `0` and `+` is an additive left cancel monoid,if it
admits an injective map that preserves `0` and `+` to an additive left cancel monoid." -/
protected abbrev addCancelMonoid [AddCancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) :
    AddCancelMonoid M₁ :=
  { hf.addLeftCancelMonoid f zero add nsmul, hf.addRightCancelMonoid f zero add nsmul with }
#align function.injective.add_cancel_monoid Function.Injective.addCancelMonoid

/-- A type endowed with `1` and `*` is a cancel monoid, if it admits an injective map that preserves
`1` and `*` to a cancel monoid. See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev cancelMonoid [CancelMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CancelMonoid M₁ :=
  { hf.leftCancelMonoid f one mul npow, hf.rightCancelMonoid f one mul npow with }
#align function.injective.cancel_monoid Function.Injective.cancelMonoid

/-- A type endowed with `0` and `+` is an additive commutative monoid, if it
admits an injective map that preserves `0` and `+` to an additive commutative monoid. -/
protected abbrev addCommMonoid [AddCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) :
    AddCommMonoid M₁ :=
  { hf.addMonoid f zero add nsmul, hf.addCommSemigroup f add with }
#align function.injective.add_comm_monoid Function.Injective.addCommMonoid

/-- A type endowed with `1` and `*` is a commutative monoid, if it admits an injective map that
preserves `1` and `*` to a commutative monoid.  See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev commMonoid [CommMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoid M₁ :=
  { hf.monoid f one mul npow, hf.commSemigroup f mul with }
#align function.injective.comm_monoid Function.Injective.commMonoid

/-- A type endowed with `0`, `1` and `+` is an additive commutative monoid with one, if it admits an
injective map that preserves `0`, `1` and `+` to an additive commutative monoid with one.
See note [reducible non-instances]. -/
protected abbrev addCommMonoidWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul ℕ M₁] [NatCast M₁]
    [AddCommMonoidWithOne M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddCommMonoidWithOne M₁ where
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)
#align function.injective.add_comm_monoid_with_one Function.Injective.addCommMonoidWithOne

/-- A type endowed with `0` and `+` is an additive cancel commutative monoid,
if it admits an injective map that preserves `0` and `+` to an additive cancel commutative monoid.
-/
protected abbrev addCancelCommMonoid [AddCancelCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : AddCancelCommMonoid M₁ :=
  { hf.addLeftCancelSemigroup f add, hf.addCommMonoid f zero add nsmul with }
#align function.injective.add_cancel_comm_monoid Function.Injective.addCancelCommMonoid

/-- A type endowed with `1` and `*` is a cancel commutative monoid, if it admits an injective map
that preserves `1` and `*` to a cancel commutative monoid.  See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev cancelCommMonoid [CancelCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CancelCommMonoid M₁ :=
  { hf.leftCancelSemigroup f mul, hf.commMonoid f one mul npow with }
#align function.injective.cancel_comm_monoid Function.Injective.cancelCommMonoid

/-- A type has an involutive negation if it admits a surjective map that
preserves `-` to a type which has an involutive negation. -/
protected abbrev involutiveNeg {M₁ : Type*} [Neg M₁] [InvolutiveNeg M₂] (f : M₁ → M₂)
    (hf : Injective f) (neg : ∀ x, f (-x) = -(f x)) : InvolutiveNeg M₁ where
  neg := Neg.neg
  neg_neg x := hf <| by rw [neg, neg, neg_neg]
#align function.injective.has_involutive_neg Function.Injective.involutiveNeg

/-- A type has an involutive inversion if it admits a surjective map that preserves `⁻¹` to a type
which has an involutive inversion. See note [reducible non-instances] -/
@[to_additive existing]
protected abbrev involutiveInv {M₁ : Type*} [Inv M₁] [InvolutiveInv M₂] (f : M₁ → M₂)
    (hf : Injective f) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) : InvolutiveInv M₁ where
  inv := Inv.inv
  inv_inv x := hf <| by rw [inv, inv, inv_inv]
#align function.injective.has_involutive_inv Function.Injective.involutiveInv

variable [Inv M₁] [Neg M₁]

/-- A type endowed with `0` and unary `-` is an `NegZeroClass`, if it admits an
injective map that preserves `0` and unary `-` to an `NegZeroClass`. -/
protected abbrev negZeroClass [NegZeroClass M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0)
    (neg : ∀ x, f (-x) = -f x) : NegZeroClass M₁ :=
  { ‹One M₁›, ‹Inv M₁› with
    neg_zero := hf <| by erw [neg, zero, neg_zero] }

/-- A type endowed with `1` and `⁻¹` is a `InvOneClass`, if it admits an injective map that
preserves `1` and `⁻¹` to a `InvOneClass`.  See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev invOneClass [InvOneClass M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (inv : ∀ x, f (x⁻¹) = (f x)⁻¹) : InvOneClass M₁ :=
  { ‹One M₁›, ‹Inv M₁› with
    inv_one := hf <| by erw [inv, one, inv_one] }

variable [Div M₁] [Pow M₁ ℤ] [Sub M₁] [SMul ℤ M₁]

/-- A type endowed with `0`, `+`, unary `-`, and binary `-` is a
`SubNegMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`, and binary `-` to
a `SubNegMonoid`. This version takes custom `nsmul` and `zsmul` as `[SMul ℕ M₁]` and `[SMul ℤ M₁]`
arguments. -/
protected abbrev subNegMonoid [SubNegMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : SubNegMonoid M₁ :=
  { hf.addMonoid f zero add nsmul, ‹Neg M₁›, ‹Sub M₁› with
    zsmul := fun n x => n • x,
    zsmul_zero' := fun x => hf <| by erw [zsmul, zero_zsmul, zero],
    zsmul_succ' := fun n x => hf <| by
      erw [zsmul, add, natCast_zsmul, succ_nsmul, zsmul, natCast_zsmul],
    zsmul_neg' := fun n x => hf <| by erw [zsmul, negSucc_zsmul, neg, zsmul, natCast_zsmul],
    sub_eq_add_neg := fun x y => hf <| by erw [sub, add, neg, sub_eq_add_neg] }
#align function.injective.sub_neg_monoid Function.Injective.subNegMonoid

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `DivInvMonoid` if it admits an injective map
that preserves `1`, `*`, `⁻¹`, and `/` to a `DivInvMonoid`. See note [reducible non-instances]. -/
@[to_additive existing subNegMonoid]
protected abbrev divInvMonoid [DivInvMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivInvMonoid M₁ :=
  { hf.monoid f one mul npow, ‹Inv M₁›, ‹Div M₁› with
    zpow := fun n x => x ^ n,
    zpow_zero' := fun x => hf <| by erw [zpow, zpow_zero, one],
    zpow_succ' := fun n x => hf <| by erw [zpow, mul, zpow_natCast, pow_succ, zpow, zpow_natCast],
    zpow_neg' := fun n x => hf <| by erw [zpow, zpow_negSucc, inv, zpow, zpow_natCast],
    div_eq_mul_inv := fun x y => hf <| by erw [div, mul, inv, div_eq_mul_inv] }
#align function.injective.div_inv_monoid Function.Injective.divInvMonoid

/-- A type endowed with `0`, `+`, unary `-`, and binary `-` is a
`SubNegZeroMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`, and binary
`-` to a `SubNegZeroMonoid`. This version takes custom `nsmul` and `zsmul` as `[SMul ℕ M₁]` and
`[SMul ℤ M₁]` arguments. -/
protected abbrev subNegZeroMonoid [SubNegZeroMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -(f x))
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : SubNegZeroMonoid M₁ :=
  { hf.subNegMonoid f zero add neg sub nsmul zsmul, hf.negZeroClass f zero neg with }

/-- A type endowed with `0`, `+`, unary `-`, and binary `-` is a
`SubNegZeroMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`, and binary
`-` to a `SubNegZeroMonoid`. This version takes custom `nsmul` and `zsmul` as `[SMul ℕ M₁]` and
`[SMul ℤ M₁]` arguments. -/
@[to_additive existing subNegMonoid]
protected abbrev divInvOneMonoid [DivInvOneMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivInvOneMonoid M₁ :=
  { hf.divInvMonoid f one mul inv div npow zpow, hf.invOneClass f one inv with }

/-- A type endowed with `0`, `+`, unary `-`, and binary `-`
is a `SubtractionMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`, and
binary `-` to a `SubtractionMonoid`. This version takes custom `nsmul` and `zsmul` as `[SMul ℕ M₁]`
and `[SMul ℤ M₁]` arguments. -/
protected abbrev subtractionMonoid [SubtractionMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : SubtractionMonoid M₁ :=
  { hf.subNegMonoid f zero add neg sub nsmul zsmul, hf.involutiveNeg f neg with
    neg_add_rev := fun x y => hf <| by erw [neg, add, neg_add_rev, add, neg, neg],
    neg_eq_of_add := fun x y h => hf <| by
      erw [neg, neg_eq_of_add_eq_zero_right (by erw [← add, h, zero])] }
#align function.injective.subtraction_monoid Function.Injective.subtractionMonoid

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `DivisionMonoid` if it admits an injective map
that preserves `1`, `*`, `⁻¹`, and `/` to a `DivisionMonoid`. See note [reducible non-instances] -/
@[to_additive existing subtractionMonoid]
protected abbrev divisionMonoid [DivisionMonoid M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivisionMonoid M₁ :=
  { hf.divInvMonoid f one mul inv div npow zpow, hf.involutiveInv f inv with
    mul_inv_rev := fun x y => hf <| by erw [inv, mul, mul_inv_rev, mul, inv, inv],
    inv_eq_of_mul := fun x y h => hf <| by
      erw [inv, inv_eq_of_mul_eq_one_right (by erw [← mul, h, one])] }
#align function.injective.division_monoid Function.Injective.divisionMonoid

/-- A type endowed with `0`, `+`, unary `-`, and binary
`-` is a `SubtractionCommMonoid` if it admits an injective map that preserves `0`, `+`, unary `-`,
and binary `-` to a `SubtractionCommMonoid`. This version takes custom `nsmul` and `zsmul` as
`[SMul ℕ M₁]` and `[SMul ℤ M₁]` arguments. -/
protected abbrev subtractionCommMonoid [SubtractionCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : SubtractionCommMonoid M₁ :=
  { hf.subtractionMonoid f zero add neg sub nsmul zsmul, hf.addCommSemigroup f add with }
#align function.injective.subtraction_comm_monoid Function.Injective.subtractionCommMonoid

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `DivisionCommMonoid` if it admits an
injective map that preserves `1`, `*`, `⁻¹`, and `/` to a `DivisionCommMonoid`.
See note [reducible non-instances]. -/
@[to_additive existing subtractionCommMonoid]
protected abbrev divisionCommMonoid [DivisionCommMonoid M₂] (f : M₁ → M₂) (hf : Injective f)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivisionCommMonoid M₁ :=
  { hf.divisionMonoid f one mul inv div npow zpow, hf.commSemigroup f mul with }
#align function.injective.division_comm_monoid Function.Injective.divisionCommMonoid

/-- A type endowed with `0` and `+` is an additive group, if it admits an
injective map that preserves `0` and `+` to an additive group. -/
protected abbrev addGroup [AddGroup M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : AddGroup M₁ :=
  { hf.subNegMonoid f zero add neg sub nsmul zsmul with
    add_left_neg := fun x => hf <| by erw [add, neg, add_left_neg, zero] }
#align function.injective.add_group Function.Injective.addGroup

/-- A type endowed with `1`, `*` and `⁻¹` is a group, if it admits an injective map that preserves
`1`, `*` and `⁻¹` to a group. See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev group [Group M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : Group M₁ :=
  { hf.divInvMonoid f one mul inv div npow zpow with
    mul_left_inv := fun x => hf <| by erw [mul, inv, mul_left_inv, one] }
#align function.injective.group Function.Injective.group

/-- A type endowed with `0`, `1` and `+` is an additive group with one, if it admits an injective
map that preserves `0`, `1` and `+` to an additive group with one.  See note
[reducible non-instances]. -/
protected abbrev addGroupWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul ℕ M₁] [Neg M₁] [Sub M₁]
    [SMul ℤ M₁] [NatCast M₁] [IntCast M₁] [AddGroupWithOne M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddGroupWithOne M₁ :=
  { hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul),
    hf.addMonoidWithOne f zero one add nsmul natCast with
    intCast := Int.cast,
    intCast_ofNat := fun n => hf (by rw [natCast, ← Int.cast, intCast, Int.cast_natCast]),
    intCast_negSucc := fun n => hf (by erw [intCast, neg, natCast, Int.cast_negSucc] ) }
#align function.injective.add_group_with_one Function.Injective.addGroupWithOne

/-- A type endowed with `0` and `+` is an additive commutative group, if it
admits an injective map that preserves `0` and `+` to an additive commutative group. -/
protected abbrev addCommGroup [AddCommGroup M₂] (f : M₁ → M₂) (hf : Injective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : AddCommGroup M₁ :=
  { hf.addCommMonoid f zero add nsmul, hf.addGroup f zero add neg sub nsmul zsmul with }
#align function.injective.add_comm_group Function.Injective.addCommGroup

/-- A type endowed with `1`, `*` and `⁻¹` is a commutative group, if it admits an injective map that
preserves `1`, `*` and `⁻¹` to a commutative group. See note [reducible non-instances]. -/
@[to_additive existing]
protected abbrev commGroup [CommGroup M₂] (f : M₁ → M₂) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroup M₁ :=
  { hf.commMonoid f one mul npow, hf.group f one mul inv div npow zpow with }
#align function.injective.comm_group Function.Injective.commGroup

/-- A type endowed with `0`, `1` and `+` is an additive commutative group with one, if it admits an
injective map that preserves `0`, `1` and `+` to an additive commutative group with one.
See note [reducible non-instances]. -/
protected abbrev addCommGroupWithOne {M₁} [Zero M₁] [One M₁] [Add M₁] [SMul ℕ M₁] [Neg M₁] [Sub M₁]
    [SMul ℤ M₁] [NatCast M₁] [IntCast M₁] [AddCommGroupWithOne M₂] (f : M₁ → M₂) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddCommGroupWithOne M₁ :=
  { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }
#align function.injective.add_comm_group_with_one Function.Injective.addCommGroupWithOne

end Injective

/-!
### Surjective
-/


namespace Surjective

variable {M₁ : Type*} {M₂ : Type*} [Mul M₂]

/-- A type endowed with `*` is a semigroup, if it admits a surjective map that preserves `*` from a
semigroup. See note [reducible non-instances]. -/
@[to_additive
"A type endowed with `+` is an additive semigroup, if it admits a
surjective map that preserves `+` from an additive semigroup."]
protected abbrev semigroup [Semigroup M₁] (f : M₁ → M₂) (hf : Surjective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : Semigroup M₂ :=
  { ‹Mul M₂› with mul_assoc := hf.forall₃.2 fun x y z => by simp only [← mul, mul_assoc] }
#align function.surjective.semigroup Function.Surjective.semigroup
#align function.surjective.add_semigroup Function.Surjective.addSemigroup

/-- A type endowed with `*` is a commutative semigroup, if it admits a surjective map that preserves
`*` from a commutative semigroup. See note [reducible non-instances]. -/
@[to_additive
"A type endowed with `+` is an additive commutative semigroup, if it admits
a surjective map that preserves `+` from an additive commutative semigroup."]
protected abbrev commMagma [CommMagma M₁] (f : M₁ → M₂) (hf : Surjective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommMagma M₂ where
  mul_comm := hf.forall₂.2 fun x y => by erw [← mul, ← mul, mul_comm]

/-- A type endowed with `*` is a commutative semigroup, if it admits a surjective map that preserves
`*` from a commutative semigroup. See note [reducible non-instances]. -/
@[to_additive
"A type endowed with `+` is an additive commutative semigroup, if it admits
a surjective map that preserves `+` from an additive commutative semigroup."]
protected abbrev commSemigroup [CommSemigroup M₁] (f : M₁ → M₂) (hf : Surjective f)
    (mul : ∀ x y, f (x * y) = f x * f y) : CommSemigroup M₂ where
  toSemigroup := hf.semigroup f mul
  __ := hf.commMagma f mul
#align function.surjective.comm_semigroup Function.Surjective.commSemigroup
#align function.surjective.add_comm_semigroup Function.Surjective.addCommSemigroup

variable [One M₂]

/-- A type endowed with `1` and `*` is a `MulOneClass`, if it admits a surjective map that preserves
`1` and `*` from a `MulOneClass`. See note [reducible non-instances]. -/
@[to_additive
"A type endowed with `0` and `+` is an `AddZeroClass`, if it admits a
surjective map that preserves `0` and `+` to an `AddZeroClass`."]
protected abbrev mulOneClass [MulOneClass M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) : MulOneClass M₂ :=
  { ‹One M₂›, ‹Mul M₂› with
    one_mul := hf.forall.2 fun x => by erw [← one, ← mul, one_mul],
    mul_one := hf.forall.2 fun x => by erw [← one, ← mul, mul_one] }
#align function.surjective.mul_one_class Function.Surjective.mulOneClass
#align function.surjective.add_zero_class Function.Surjective.addZeroClass

variable [Pow M₂ ℕ]

/-- A type endowed with `1` and `*` is a monoid, if it admits a surjective map that preserves `1`
and `*` to a monoid. See note [reducible non-instances]. -/
@[to_additive
"A type endowed with `0` and `+` is an additive monoid, if it admits a
surjective map that preserves `0` and `+` to an additive monoid. This version takes a custom `nsmul`
as a `[SMul ℕ M₂]` argument."]
protected abbrev monoid [Monoid M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : Monoid M₂ :=
  { hf.semigroup f mul, hf.mulOneClass f one mul with
    npow := fun n x => x ^ n,
    npow_zero := hf.forall.2 fun x => by dsimp only; erw [← npow, pow_zero, ← one],
    npow_succ := fun n => hf.forall.2 fun x => by
      dsimp only
      erw [← npow, pow_succ, ← npow, ← mul] }
#align function.surjective.monoid Function.Surjective.monoid
#align function.surjective.add_monoid Function.Surjective.addMonoid

/-- A type endowed with `0`, `1` and `+` is an additive monoid with one, if it admits a surjective
map that preserves `0`, `1` and `*` from an additive monoid with one. See note
[reducible non-instances]. -/
protected abbrev addMonoidWithOne {M₂} [Zero M₂] [One M₂] [Add M₂] [SMul ℕ M₂] [NatCast M₂]
    [AddMonoidWithOne M₁] (f : M₁ → M₂) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddMonoidWithOne M₂ :=
  { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := by rw [← Nat.cast, ← natCast, Nat.cast_zero, zero]
    natCast_succ := fun n => by rw [← Nat.cast, ← natCast, Nat.cast_succ, add, one, natCast]
    one := 1 }
#align function.surjective.add_monoid_with_one Function.Surjective.addMonoidWithOne

/-- A type endowed with `1` and `*` is a commutative monoid, if it admits a surjective map that
preserves `1` and `*` from a commutative monoid. See note [reducible non-instances]. -/
@[to_additive
"A type endowed with `0` and `+` is an additive commutative monoid, if it
admits a surjective map that preserves `0` and `+` to an additive commutative monoid."]
protected abbrev commMonoid [CommMonoid M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoid M₂ :=
  { hf.commSemigroup f mul, hf.monoid f one mul npow with }
#align function.surjective.comm_monoid Function.Surjective.commMonoid
#align function.surjective.add_comm_monoid Function.Surjective.addCommMonoid

/-- A type endowed with `0`, `1` and `+` is an additive monoid with one,
if it admits a surjective map that preserves `0`, `1` and `*` from an additive monoid with one.
See note [reducible non-instances]. -/
protected abbrev addCommMonoidWithOne {M₂} [Zero M₂] [One M₂] [Add M₂] [SMul ℕ M₂] [NatCast M₂]
    [AddCommMonoidWithOne M₁] (f : M₁ → M₂) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddCommMonoidWithOne M₂ where
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)
#align function.surjective.add_comm_monoid_with_one Function.Surjective.addCommMonoidWithOne

/-- A type has an involutive inversion if it admits a surjective map that preserves `⁻¹` to a type
which has an involutive inversion. See note [reducible non-instances] -/
@[to_additive
"A type has an involutive negation if it admits a surjective map that
preserves `-` to a type which has an involutive negation."]
protected abbrev involutiveInv {M₂ : Type*} [Inv M₂] [InvolutiveInv M₁] (f : M₁ → M₂)
    (hf : Surjective f) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) : InvolutiveInv M₂ where
  inv := Inv.inv
  inv_inv := hf.forall.2 fun x => by erw [← inv, ← inv, inv_inv]
#align function.surjective.has_involutive_inv Function.Surjective.involutiveInv
#align function.surjective.has_involutive_neg Function.Surjective.involutiveNeg

variable [Inv M₂] [Div M₂] [Pow M₂ ℤ]

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a `DivInvMonoid` if it admits a surjective map
that preserves `1`, `*`, `⁻¹`, and `/` to a `DivInvMonoid`. See note [reducible non-instances]. -/
@[to_additive subNegMonoid
"A type endowed with `0`, `+`, unary `-`, and binary `-` is a
`SubNegMonoid` if it admits a surjective map that preserves `0`, `+`, unary `-`, and binary `-` to
a `SubNegMonoid`."]
protected abbrev divInvMonoid [DivInvMonoid M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : DivInvMonoid M₂ :=
  { hf.monoid f one mul npow, ‹Div M₂›, ‹Inv M₂› with
    zpow := fun n x => x ^ n,
    zpow_zero' := hf.forall.2 fun x => by dsimp only; erw [← zpow, zpow_zero, ← one],
    zpow_succ' := fun n => hf.forall.2 fun x => by
      dsimp only
      erw [← zpow, ← zpow, zpow_natCast, zpow_natCast, pow_succ, ← mul],
    zpow_neg' := fun n => hf.forall.2 fun x => by
      dsimp only
      erw [← zpow, ← zpow, zpow_negSucc, zpow_natCast, inv],
    div_eq_mul_inv := hf.forall₂.2 fun x y => by erw [← inv, ← mul, ← div, div_eq_mul_inv] }
#align function.surjective.div_inv_monoid Function.Surjective.divInvMonoid
#align function.surjective.sub_neg_monoid Function.Surjective.subNegMonoid

/-- A type endowed with `1`, `*` and `⁻¹` is a group, if it admits a surjective map that preserves
`1`, `*` and `⁻¹` to a group. See note [reducible non-instances]. -/
@[to_additive
"A type endowed with `0` and `+` is an additive group, if it admits a
surjective map that preserves `0` and `+` to an additive group."]
protected abbrev group [Group M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : Group M₂ :=
  { hf.divInvMonoid f one mul inv div npow zpow with
    mul_left_inv := hf.forall.2 fun x => by erw [← inv, ← mul, mul_left_inv, one] }
#align function.surjective.group Function.Surjective.group
#align function.surjective.add_group Function.Surjective.addGroup

/-- A type endowed with `0`, `1`, `+` is an additive group with one,
if it admits a surjective map that preserves `0`, `1`, and `+` to an additive group with one.
See note [reducible non-instances]. -/
protected abbrev addGroupWithOne {M₂} [Zero M₂] [One M₂] [Add M₂] [Neg M₂] [Sub M₂] [SMul ℕ M₂]
    [SMul ℤ M₂] [NatCast M₂] [IntCast M₂] [AddGroupWithOne M₁] (f : M₁ → M₂) (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddGroupWithOne M₂ :=
  { hf.addMonoidWithOne f zero one add nsmul natCast,
    hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul) with
    intCast := Int.cast,
    intCast_ofNat := fun n => by rw [← Int.cast, ← intCast, Int.cast_natCast, natCast],
    intCast_negSucc := fun n => by
      rw [← Int.cast, ← intCast, Int.cast_negSucc, neg, natCast] }
#align function.surjective.add_group_with_one Function.Surjective.addGroupWithOne

/-- A type endowed with `1`, `*`, `⁻¹`, and `/` is a commutative group, if it admits a surjective
map that preserves `1`, `*`, `⁻¹`, and `/` from a commutative group. See note
[reducible non-instances]. -/
@[to_additive
"A type endowed with `0` and `+` is an additive commutative group, if it
admits a surjective map that preserves `0` and `+` to an additive commutative group."]
protected abbrev commGroup [CommGroup M₁] (f : M₁ → M₂) (hf : Surjective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroup M₂ :=
  { hf.commMonoid f one mul npow, hf.group f one mul inv div npow zpow with }
#align function.surjective.comm_group Function.Surjective.commGroup
#align function.surjective.add_comm_group Function.Surjective.addCommGroup

/-- A type endowed with `0`, `1`, `+` is an additive commutative group with one, if it admits a
surjective map that preserves `0`, `1`, and `+` to an additive commutative group with one.
See note [reducible non-instances]. -/
protected abbrev addCommGroupWithOne {M₂} [Zero M₂] [One M₂] [Add M₂] [Neg M₂] [Sub M₂] [SMul ℕ M₂]
    [SMul ℤ M₂] [NatCast M₂] [IntCast M₂] [AddCommGroupWithOne M₁] (f : M₁ → M₂) (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddCommGroupWithOne M₂ :=
  { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }
#align function.surjective.add_comm_group_with_one Function.Surjective.addCommGroupWithOne

end Surjective

end Function
