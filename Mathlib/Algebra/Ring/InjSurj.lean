/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Data.Int.Cast.Basic

/-!
# Pulling back rings along injective maps, and pushing them forward along surjective maps

## Implementation note

The `nsmul` and `zsmul` assumptions on any transfer definition for an algebraic structure involving
both addition and multiplication (e.g. `AddMonoidWithOne`) is `∀ n x, f (n • x) = n • f x`, which is
what we would expect.
However, we cannot do the same for transfer definitions built using `to_additive` (e.g. `AddMonoid`)
as we want the multiplicative versions to be `∀ x n, f (x ^ n) = f x ^ n`.
As a result, we must use `Function.swap` when using additivised transfer definitions in
non-additivised ones.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

variable {R S : Type*}

namespace Function.Injective
variable (f : S → R) (hf : Injective f)
include hf

variable [Add S] [Mul S]

/-- Pullback a `LeftDistribClass` instance along an injective function. -/
theorem leftDistribClass [Mul R] [Add R] [LeftDistribClass R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftDistribClass S where
  left_distrib x y z := hf <| by simp only [*, left_distrib]

/-- Pullback a `RightDistribClass` instance along an injective function. -/
theorem rightDistribClass [Mul R] [Add R] [RightDistribClass R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightDistribClass S where
  right_distrib x y z := hf <| by simp only [*, right_distrib]

variable [Zero S] [One S] [Neg S] [Sub S] [SMul ℕ S] [SMul ℤ S]
  [Pow S ℕ] [NatCast S] [IntCast S]

/-- Pullback a `Distrib` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev distrib [Distrib R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : Distrib S where
  __ := hf.leftDistribClass f add mul
  __ := hf.rightDistribClass f add mul

/-- A type endowed with `-` and `*` has distributive negation, if it admits an injective map that
preserves `-` and `*` to a type which has distributive negation. -/
-- See note [reducible non-instances]
protected abbrev hasDistribNeg (f : S → R) (hf : Injective f) [Mul R] [HasDistribNeg R]
    (neg : ∀ a, f (-a) = -f a)
    (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg S :=
  { hf.involutiveNeg _ neg, ‹Mul S› with
    neg_mul := fun x y => hf <| by rw [neg, mul, neg, neg_mul, mul],
    mul_neg := fun x y => hf <| by rw [neg, mul, neg, mul_neg, mul] }

/-- A type endowed with `0`, `1` and `+` is an additive monoid with one,
if it admits an injective map that preserves `0`, `1` and `+` to an additive monoid with one.
See note [reducible non-instances]. -/
protected abbrev addMonoidWithOne [AddMonoidWithOne R]
    (f : S → R) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddMonoidWithOne S :=
  { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := hf (by rw [natCast, Nat.cast_zero, zero]),
    natCast_succ := fun n => hf (by rw [natCast, Nat.cast_succ, add, one, natCast]) }

/-- A type endowed with `0`, `1` and `+` is an additive commutative monoid with one, if it admits an
injective map that preserves `0`, `1` and `+` to an additive commutative monoid with one.
See note [reducible non-instances]. -/
protected abbrev addCommMonoidWithOne {S} [Zero S] [One S] [Add S] [SMul ℕ S] [NatCast S]
    [AddCommMonoidWithOne R] (f : S → R) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddCommMonoidWithOne S where
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)

/-- A type endowed with `0`, `1` and `+` is an additive group with one, if it admits an injective
map that preserves `0`, `1` and `+` to an additive group with one.  See note
[reducible non-instances]. -/
protected abbrev addGroupWithOne {S} [Zero S] [One S] [Add S] [SMul ℕ S] [Neg S] [Sub S]
    [SMul ℤ S] [NatCast S] [IntCast S] [AddGroupWithOne R] (f : S → R) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddGroupWithOne S :=
  { hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul),
    hf.addMonoidWithOne f zero one add nsmul natCast with
    intCast := Int.cast,
    intCast_ofNat := fun n => hf (by rw [natCast, intCast, Int.cast_natCast]),
    intCast_negSucc := fun n => hf (by rw [intCast, neg, natCast, Int.cast_negSucc]) }

/-- A type endowed with `0`, `1` and `+` is an additive commutative group with one, if it admits an
injective map that preserves `0`, `1` and `+` to an additive commutative group with one.
See note [reducible non-instances]. -/
protected abbrev addCommGroupWithOne {S} [Zero S] [One S] [Add S] [SMul ℕ S] [Neg S] [Sub S]
    [SMul ℤ S] [NatCast S] [IntCast S] [AddCommGroupWithOne R] (f : S → R) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddCommGroupWithOne S :=
  { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }

/-- Pullback a `NonUnitalNonAssocSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalNonAssocSemiring S where
  toAddCommMonoid := hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul

/-- Pullback a `NonUnitalSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalSemiring [NonUnitalSemiring R]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) :
    NonUnitalSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul

/-- Pullback a `NonAssocSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonAssocSemiring [NonAssocSemiring R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : NonAssocSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul natCast

/-- Pullback a `Semiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev semiring [Semiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) : Semiring S where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.monoidWithZero f zero one mul npow

/-- Pullback a `NonUnitalNonAssocRing` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing R] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalNonAssocRing S where
  toAddCommGroup := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul

/-- Pullback a `NonUnitalRing` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalRing [NonUnitalRing R]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul

/-- Pullback a `NonAssocRing` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonAssocRing [NonAssocRing R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : NonAssocRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast

/-- Pullback a `Ring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev ring [Ring R] (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : Ring S where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  -- zsmul included here explicitly to make sure it's picked correctly by `fast_instance%`.
  zsmul := fun n x ↦ n • x
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)

/-- Pullback a `NonUnitalNonAssocCommSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring R]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) :
    NonUnitalNonAssocCommSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

/-- Pullback a `NonUnitalCommSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring R] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) :
    NonUnitalCommSemiring S where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul

/-- Pullback a `NonAssocCommSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonAssocCommSemiring [NonAssocCommSemiring R] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : NonAssocCommSemiring S where
  toNonAssocSemiring := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.commMagma f mul

/-- Pullback a `CommSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev commSemiring [CommSemiring R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n) :
    CommSemiring S where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.commSemigroup f mul

/-- Pullback a `NonUnitalNonAssocCommRing` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing R] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

/-- Pullback a `NonUnitalCommRing` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalCommRing [NonUnitalCommRing R] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalCommRing S where
  toNonUnitalRing := hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

/-- Pullback a `NonAssocCommRing` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonAssocCommRing [NonAssocCommRing R] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : NonAssocCommRing S where
  toNonAssocRing := hf.nonAssocRing f zero one add mul neg sub nsmul zsmul natCast intCast
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

/-- Pullback a `CommRing` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev commRing [CommRing R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : CommRing S where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commMonoid f one mul npow

end Function.Injective

namespace Function.Surjective
variable (f : R → S) (hf : Surjective f)
include hf

variable [Add S] [Mul S]

/-- Pushforward a `LeftDistribClass` instance along a surjective function. -/
theorem leftDistribClass [Mul R] [Add R] [LeftDistribClass R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftDistribClass S where
  left_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, left_distrib]

/-- Pushforward a `RightDistribClass` instance along a surjective function. -/
theorem rightDistribClass [Mul R] [Add R] [RightDistribClass R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightDistribClass S where
  right_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, right_distrib]

/-- Pushforward a `Distrib` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev distrib [Distrib R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : Distrib S where
  __ := hf.leftDistribClass f add mul
  __ := hf.rightDistribClass f add mul

variable [Zero S] [One S] [Neg S] [Sub S] [SMul ℕ S] [SMul ℤ S]
  [Pow S ℕ] [NatCast S] [IntCast S]

/-- A type endowed with `-` and `*` has distributive negation, if it admits a surjective map that
preserves `-` and `*` from a type which has distributive negation. -/
-- See note [reducible non-instances]
protected abbrev hasDistribNeg [Mul R] [HasDistribNeg R]
    (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg S :=
  { hf.involutiveNeg _ neg, ‹Mul S› with
    neg_mul := hf.forall₂.2 fun x y => by rw [← neg, ← mul, neg_mul, neg, mul]
    mul_neg := hf.forall₂.2 fun x y => by rw [← neg, ← mul, mul_neg, neg, mul] }


/-- A type endowed with `0`, `1` and `+` is an additive monoid with one, if it admits a surjective
map that preserves `0`, `1` and `*` from an additive monoid with one. See note
[reducible non-instances]. -/
protected abbrev addMonoidWithOne [AddMonoidWithOne R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddMonoidWithOne S :=
  { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := by rw [← natCast, Nat.cast_zero, zero]
    natCast_succ := fun n => by rw [← natCast, Nat.cast_succ, add, one, natCast] }

/-- A type endowed with `0`, `1` and `+` is an additive monoid with one,
if it admits a surjective map that preserves `0`, `1` and `*` from an additive monoid with one.
See note [reducible non-instances]. -/
protected abbrev addCommMonoidWithOne [AddCommMonoidWithOne R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddCommMonoidWithOne S where
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)

/-- A type endowed with `0`, `1`, `+` is an additive group with one,
if it admits a surjective map that preserves `0`, `1`, and `+` to an additive group with one.
See note [reducible non-instances]. -/
protected abbrev addGroupWithOne [AddGroupWithOne R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddGroupWithOne S :=
  { hf.addMonoidWithOne f zero one add nsmul natCast,
    hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul) with
    intCast := Int.cast,
    intCast_ofNat := fun n => by rw [← intCast, Int.cast_natCast, natCast],
    intCast_negSucc := fun n => by
      rw [← intCast, Int.cast_negSucc, neg, natCast] }

/-- A type endowed with `0`, `1`, `+` is an additive commutative group with one, if it admits a
surjective map that preserves `0`, `1`, and `+` to an additive commutative group with one.
See note [reducible non-instances]. -/
protected abbrev addCommGroupWithOne [AddCommGroupWithOne R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddCommGroupWithOne S :=
  { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }

/-- Pushforward a `NonUnitalNonAssocSemiring` instance along a surjective function.
See note [reducible non-instances]. -/
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalNonAssocSemiring S where
  toAddCommMonoid := hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul

/-- Pushforward a `NonUnitalSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalSemiring [NonUnitalSemiring R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul

/-- Pushforward a `NonAssocSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonAssocSemiring [NonAssocSemiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : NonAssocSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul natCast

/-- Pushforward a `Semiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev semiring [Semiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n) : Semiring S where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.monoidWithZero f zero one mul npow

/-- Pushforward a `NonUnitalNonAssocRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalNonAssocRing S where
  toAddCommGroup := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul

/-- Pushforward a `NonUnitalRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalRing [NonUnitalRing R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul

/-- Pushforward a `NonAssocRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonAssocRing [NonAssocRing R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : NonAssocRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast

/-- Pushforward a `Ring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev ring [Ring R] (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : Ring S where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)

/-- Pushforward a `NonUnitalNonAssocCommSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

/-- Pushforward a `NonUnitalCommSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalCommSemiring S where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul

/-- Pushforward a `NonAssocCommSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonAssocCommSemiring [NonAssocCommSemiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : NonAssocCommSemiring S where
  toNonAssocSemiring := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.commMagma f mul

/-- Pushforward a `CommSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev commSemiring [CommSemiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) : CommSemiring S where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.commSemigroup f mul

/-- Pushforward a `NonUnitalNonAssocCommRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing R]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

/-- Pushforward a `NonUnitalCommRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalCommRing [NonUnitalCommRing R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalCommRing S where
  toNonUnitalRing := hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

/-- Pushforward a `NonAssocCommRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonAssocCommRing [NonAssocCommRing R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : NonAssocCommRing S where
  toNonAssocRing := hf.nonAssocRing f zero one add mul neg sub nsmul zsmul natCast intCast
  __ := hf.nonAssocCommSemiring f zero one add mul nsmul natCast

/-- Pushforward a `CommRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev commRing [CommRing R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : CommRing S where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commMonoid f one mul npow

end Function.Surjective

variable [Mul R] [HasDistribNeg R]

instance AddOpposite.instHasDistribNeg : HasDistribNeg Rᵃᵒᵖ :=
  unop_injective.hasDistribNeg _ unop_neg unop_mul
