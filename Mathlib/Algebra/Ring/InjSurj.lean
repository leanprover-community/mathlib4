/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Opposites
import Mathlib.Algebra.GroupWithZero.InjSurj

#align_import algebra.ring.inj_surj from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Pulling back rings along injective maps, and pushing them forward along surjective maps.

-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

/-!
### `Distrib` class
-/


/-- Pullback a `Distrib` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.distrib {S} [Mul R] [Add R] [Distrib S] (f : R → S)
    (hf : Injective f) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
    Distrib R where
  mul := (· * ·)
  add := (· + ·)
  left_distrib x y z := hf <| by simp only [*, left_distrib]
  right_distrib x y z := hf <| by simp only [*, right_distrib]
#align function.injective.distrib Function.Injective.distrib

/-- Pushforward a `Distrib` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.distrib {S} [Distrib R] [Add S] [Mul S] (f : R → S)
    (hf : Surjective f) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) :
    Distrib S where
  mul := (· * ·)
  add := (· + ·)
  left_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, left_distrib]
  right_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, right_distrib]
#align function.surjective.distrib Function.Surjective.distrib

section InjectiveSurjectiveMaps

/-!
### Semirings
-/

variable [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [SMul ℕ β] [SMul ℤ β] [Pow β ℕ]
  [NatCast β] [IntCast β]

/-- Pullback a `NonUnitalNonAssocSemiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalNonAssocSemiring {α : Type u}
    [NonUnitalNonAssocSemiring α] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalNonAssocSemiring β where
  toAddCommMonoid := hf.addCommMonoid f zero add nsmul
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul
#align function.injective.non_unital_non_assoc_semiring Function.Injective.nonUnitalNonAssocSemiring

/-- Pullback a `NonUnitalSemiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalSemiring {α : Type u} [NonUnitalSemiring α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) :
    NonUnitalSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul
#align function.injective.non_unital_semiring Function.Injective.nonUnitalSemiring

/-- Pullback a `NonAssocSemiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonAssocSemiring {α : Type u} [NonAssocSemiring α] {β : Type v}
    [Zero β] [One β] [Mul β] [Add β] [SMul ℕ β] [NatCast β] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (nat_cast : ∀ n : ℕ, f n = n) : NonAssocSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul nat_cast
#align function.injective.non_assoc_semiring Function.Injective.nonAssocSemiring

/-- Pullback a `Semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.semiring {α : Type u} [Semiring α] {β : Type v} [Zero β] [One β]
    [Add β] [Mul β] [Pow β ℕ] [SMul ℕ β] [NatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : Semiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul nat_cast
  __ := hf.monoidWithZero f zero one mul npow
#align function.injective.semiring Function.Injective.semiring

/-- Pushforward a `NonUnitalNonAssocSemiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalNonAssocSemiring {α : Type u}
    [NonUnitalNonAssocSemiring α] (f : α → β) (hf : Surjective f) (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalNonAssocSemiring β where
  toAddCommMonoid := hf.addCommMonoid f zero add nsmul
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul
#align function.surjective.non_unital_non_assoc_semiring Function.Surjective.nonUnitalNonAssocSemiring

/-- Pushforward a `NonUnitalSemiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalSemiring {α : Type u} [NonUnitalSemiring α] (f : α → β)
    (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) :
    NonUnitalSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul
#align function.surjective.non_unital_semiring Function.Surjective.nonUnitalSemiring

/-- Pushforward a `NonAssocSemiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonAssocSemiring {α : Type u} [NonAssocSemiring α] {β : Type v}
    [Zero β] [One β] [Add β] [Mul β] [SMul ℕ β] [NatCast β] (f : α → β) (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (nat_cast : ∀ n : ℕ, f n = n) : NonAssocSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul nat_cast
#align function.surjective.non_assoc_semiring Function.Surjective.nonAssocSemiring

/-- Pushforward a `Semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.semiring {α : Type u} [Semiring α] {β : Type v} [Zero β] [One β]
    [Add β] [Mul β] [Pow β ℕ] [SMul ℕ β] [NatCast β] (f : α → β) (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) : Semiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul nat_cast
  __ := hf.monoidWithZero f zero one mul npow
#align function.surjective.semiring Function.Surjective.semiring

/-- Pullback a `NonUnitalNonAssocRing` instance along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Injective.nonUnitalNonAssocRing [NonUnitalNonAssocRing α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalNonAssocRing β where
  toAddCommGroup := hf.addCommGroup f zero add neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
#align function.injective.non_unital_non_assoc_ring Function.Injective.nonUnitalNonAssocRing

/-- Pushforward a `NonUnitalNonAssocRing` instance along a surjective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Surjective.nonUnitalNonAssocRing [NonUnitalNonAssocRing α] (f : α → β)
    (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalNonAssocRing β where
  toAddCommGroup := hf.addCommGroup f zero add neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
#align function.surjective.non_unital_non_assoc_ring Function.Surjective.nonUnitalNonAssocRing

/-- Pullback a `NonUnitalRing` instance along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Injective.nonUnitalRing [NonUnitalRing α] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) :
    NonUnitalRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul
#align function.injective.non_unital_ring Function.Injective.nonUnitalRing

/-- Pushforward a `NonUnitalRing` instance along a surjective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Surjective.nonUnitalRing [NonUnitalRing α] (f : α → β) (hf : Surjective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) :
    NonUnitalRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul
#align function.surjective.non_unital_ring Function.Surjective.nonUnitalRing

/-- Pullback a `NonAssocRing` instance along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Injective.nonAssocRing [NonAssocRing α] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) : NonAssocRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul nat_cast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast
#align function.injective.non_assoc_ring Function.Injective.nonAssocRing

/-- Pushforward a `NonAssocRing` instance along a surjective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Surjective.nonAssocRing [NonAssocRing α] (f : α → β) (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) : NonAssocRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul nat_cast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast
#align function.surjective.non_assoc_ring Function.Surjective.nonAssocRing

/-- Pullback a `Ring` instance along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Injective.ring [Ring α] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) : Ring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow nat_cast
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast
  __ := hf.addCommGroup f zero add neg sub nsmul zsmul
#align function.injective.ring Function.Injective.ring

/-- Pushforward a `Ring` instance along a surjective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Surjective.ring [Ring α] (f : α → β) (hf : Surjective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) : Ring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow nat_cast
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast
  __ := hf.addCommGroup f zero add neg sub nsmul zsmul
#align function.surjective.ring Function.Surjective.ring

/-- Pullback a `NonUnitalNonAssocCommSemiring` instance along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Injective.nonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring α]
    (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) :
    NonUnitalNonAssocCommSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

/-- Pushforward a `NonUnitalNonAssocCommSemiring` instance along a surjective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Surjective.nonUnitalNonAssocCommSemiring  [NonUnitalNonAssocCommSemiring α]
    (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) :
    NonUnitalNonAssocCommSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

/-- Pullback a `NonUnitalCommSemiring` instance along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Injective.nonUnitalCommSemiring [NonUnitalCommSemiring α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) :
    NonUnitalCommSemiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul
#align function.injective.non_unital_comm_semiring Function.Injective.nonUnitalCommSemiring

/-- Pushforward a `NonUnitalCommSemiring` instance along a surjective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Surjective.nonUnitalCommSemiring [NonUnitalCommSemiring α] (f : α → β)
    (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) :
    NonUnitalCommSemiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul
#align function.surjective.non_unital_comm_semiring Function.Surjective.nonUnitalCommSemiring

-- `NonAssocCommSemiring` currently doesn't exist

/-- Pullback a `CommSemiring` instance along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Injective.commSemiring [CommSemiring α] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) :
    CommSemiring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow nat_cast
  __ := hf.commSemigroup f mul
#align function.injective.comm_semiring Function.Injective.commSemiring

/-- Pushforward a `NonAssocSemiring` instance along a surjective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Surjective.commSemiring [CommSemiring α] (f : α → β) (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) :
    CommSemiring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow nat_cast
  __ := hf.commSemigroup f mul
#align function.surjective.comm_semiring Function.Surjective.commSemiring

/-- Pullback a `NonUnitalNonAssocCommRing` instance along an injective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Injective.nonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalNonAssocCommRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

/-- Pushforward a `NonUnitalNonAssocCommRing` instance along a surjective function. -/
@[reducible] -- See note [reducible non-instances]
protected def Function.Surjective.nonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing α]
    (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalNonAssocCommRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

/-- Pullback a `NonUnitalCommRing` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalCommRing [NonUnitalCommRing α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalCommRing β where
  toNonUnitalRing := hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul
#align function.injective.non_unital_comm_ring Function.Injective.nonUnitalCommRing

/-- Pushforward a `NonUnitalCommRing` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalCommRing [NonUnitalCommRing α] (f : α → β)
    (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalCommRing β where
  toNonUnitalRing := hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul
#align function.surjective.non_unital_comm_ring Function.Surjective.nonUnitalCommRing

/-- Pullback a `CommRing` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commRing [CommRing α] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : CommRing β where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast
  __ := hf.commMonoid f one mul npow
#align function.injective.comm_ring Function.Injective.commRing

/-- Pushforward a `CommRing` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commRing [CommRing α] (f : α → β) (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : CommRing β where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast
  __ := hf.commMonoid f one mul npow
#align function.surjective.comm_ring Function.Surjective.commRing

end InjectiveSurjectiveMaps

section HasDistribNeg
variable [Mul α] [HasDistribNeg α]

-- See note [reducible non-instances]
/-- A type endowed with `-` and `*` has distributive negation, if it admits an injective map that
preserves `-` and `*` to a type which has distributive negation. -/
@[reducible]
protected def Function.Injective.hasDistribNeg [Neg β] [Mul β] (f : β → α) (hf : Injective f)
    (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg β :=
  { hf.involutiveNeg _ neg, ‹Mul β› with
    neg_mul := fun x y => hf <| by erw [neg, mul, neg, neg_mul, mul],
    mul_neg := fun x y => hf <| by erw [neg, mul, neg, mul_neg, mul] }
#align function.injective.has_distrib_neg Function.Injective.hasDistribNeg

-- See note [reducible non-instances]
/-- A type endowed with `-` and `*` has distributive negation, if it admits a surjective map that
preserves `-` and `*` from a type which has distributive negation. -/
@[reducible]
protected def Function.Surjective.hasDistribNeg [Neg β] [Mul β] (f : α → β) (hf : Surjective f)
    (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg β :=
  { hf.involutiveNeg _ neg, ‹Mul β› with
    neg_mul := hf.forall₂.2 fun x y => by erw [← neg, ← mul, neg_mul, neg, mul]
    mul_neg := hf.forall₂.2 fun x y => by erw [← neg, ← mul, mul_neg, neg, mul] }
#align function.surjective.has_distrib_neg Function.Surjective.hasDistribNeg

instance AddOpposite.instHasDistribNeg : HasDistribNeg αᵃᵒᵖ :=
  unop_injective.hasDistribNeg _ unop_neg unop_mul

end HasDistribNeg
