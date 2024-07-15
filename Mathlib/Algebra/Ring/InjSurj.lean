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
# Pulling back rings along injective maps, and pushing them forward along surjective maps
-/

variable {α β : Type*} [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [SMul ℕ β] [SMul ℤ β]
  [Pow β ℕ] [NatCast β] [IntCast β]

namespace Function.Injective
variable (f : β → α) (hf : Injective f)

/-- Pullback a `LeftDistribClass` instance along an injective function. -/
theorem leftDistribClass [Mul α] [Add α] [LeftDistribClass α] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftDistribClass β where
  left_distrib x y z := hf <| by simp only [*, left_distrib]

/-- Pullback a `RightDistribClass` instance along an injective function. -/
theorem rightDistribClass [Mul α] [Add α] [RightDistribClass α] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightDistribClass β where
  right_distrib x y z := hf <| by simp only [*, right_distrib]

/-- Pullback a `Distrib` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev distrib [Distrib α] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : Distrib β where
  __ := hf.leftDistribClass f add mul
  __ := hf.rightDistribClass f add mul
#align function.injective.distrib Function.Injective.distrib

/-- A type endowed with `-` and `*` has distributive negation, if it admits an injective map that
preserves `-` and `*` to a type which has distributive negation. -/
-- -- See note [reducible non-instances]
protected abbrev hasDistribNeg [Mul α] [HasDistribNeg α] (neg : ∀ a, f (-a) = -f a)
    (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg β :=
  { hf.involutiveNeg _ neg, ‹Mul β› with
    neg_mul := fun x y => hf <| by erw [neg, mul, neg, neg_mul, mul],
    mul_neg := fun x y => hf <| by erw [neg, mul, neg, mul_neg, mul] }
#align function.injective.has_distrib_neg Function.Injective.hasDistribNeg

/-- Pullback a `NonUnitalNonAssocSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalNonAssocSemiring β where
  toAddCommMonoid := hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul
#align function.injective.non_unital_non_assoc_semiring Function.Injective.nonUnitalNonAssocSemiring

/-- Pullback a `NonUnitalSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalSemiring [NonUnitalSemiring α]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) :
    NonUnitalSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul
#align function.injective.non_unital_semiring Function.Injective.nonUnitalSemiring

/-- Pullback a `NonAssocSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonAssocSemiring [NonAssocSemiring α]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : NonAssocSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
#align function.injective.non_assoc_semiring Function.Injective.nonAssocSemiring

/-- Pullback a `Semiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev semiring [Semiring α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) : Semiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.monoidWithZero f zero one mul npow
#align function.injective.semiring Function.Injective.semiring

/-- Pullback a `NonUnitalNonAssocRing` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalNonAssocRing β where
  toAddCommGroup := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
#align function.injective.non_unital_non_assoc_ring Function.Injective.nonUnitalNonAssocRing

/-- Pullback a `NonUnitalRing` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalRing [NonUnitalRing α]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul
#align function.injective.non_unital_ring Function.Injective.nonUnitalRing

/-- Pullback a `NonAssocRing` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonAssocRing [NonAssocRing α]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : NonAssocRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
#align function.injective.non_assoc_ring Function.Injective.nonAssocRing

/-- Pullback a `Ring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev ring [Ring α] (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : Ring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
#align function.injective.ring Function.Injective.ring

/-- Pullback a `NonUnitalNonAssocCommSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring α]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) :
    NonUnitalNonAssocCommSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

/-- Pullback a `NonUnitalCommSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) :
    NonUnitalCommSemiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul
#align function.injective.non_unital_comm_semiring Function.Injective.nonUnitalCommSemiring

-- `NonAssocCommSemiring` currently doesn't exist

/-- Pullback a `CommSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev commSemiring [CommSemiring α]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n) :
    CommSemiring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.commSemigroup f mul
#align function.injective.comm_semiring Function.Injective.commSemiring

/-- Pullback a `NonUnitalNonAssocCommRing` instance along an injective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

/-- Pullback a `NonUnitalCommRing` instance along an injective function. -/
-- -- See note [reducible non-instances]
protected abbrev nonUnitalCommRing [NonUnitalCommRing α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalCommRing β where
  toNonUnitalRing := hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul
#align function.injective.non_unital_comm_ring Function.Injective.nonUnitalCommRing

/-- Pullback a `CommRing` instance along an injective function. -/
-- -- See note [reducible non-instances]
protected abbrev commRing [CommRing α]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : CommRing β where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commMonoid f one mul npow
#align function.injective.comm_ring Function.Injective.commRing

end Function.Injective

namespace Function.Surjective
variable (f : α → β) (hf : Surjective f)

/-- Pushforward a `LeftDistribClass` instance along a surjective function. -/
theorem leftDistribClass [Mul α] [Add α] [LeftDistribClass α] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftDistribClass β where
  left_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, left_distrib]

/-- Pushforward a `RightDistribClass` instance along a surjective function. -/
theorem rightDistribClass [Mul α] [Add α] [RightDistribClass α] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightDistribClass β where
  right_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, right_distrib]

/-- Pushforward a `Distrib` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev distrib [Distrib α] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : Distrib β where
  __ := hf.leftDistribClass f add mul
  __ := hf.rightDistribClass f add mul
#align function.surjective.distrib Function.Surjective.distrib

/-- A type endowed with `-` and `*` has distributive negation, if it admits a surjective map that
preserves `-` and `*` from a type which has distributive negation. -/
-- See note [reducible non-instances]
protected abbrev hasDistribNeg [Mul α] [HasDistribNeg α]
    (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg β :=
  { hf.involutiveNeg _ neg, ‹Mul β› with
    neg_mul := hf.forall₂.2 fun x y => by erw [← neg, ← mul, neg_mul, neg, mul]
    mul_neg := hf.forall₂.2 fun x y => by erw [← neg, ← mul, mul_neg, neg, mul] }
#align function.surjective.has_distrib_neg Function.Surjective.hasDistribNeg

/-- Pushforward a `NonUnitalNonAssocSemiring` instance along a surjective function.
See note [reducible non-instances]. -/
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalNonAssocSemiring β where
  toAddCommMonoid := hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul
#align function.surjective.non_unital_non_assoc_semiring Function.Surjective.nonUnitalNonAssocSemiring

/-- Pushforward a `NonUnitalSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalSemiring [NonUnitalSemiring α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul
#align function.surjective.non_unital_semiring Function.Surjective.nonUnitalSemiring

/-- Pushforward a `NonAssocSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonAssocSemiring [NonAssocSemiring α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : NonAssocSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
#align function.surjective.non_assoc_semiring Function.Surjective.nonAssocSemiring

/-- Pushforward a `Semiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev semiring [Semiring α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n) : Semiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.monoidWithZero f zero one mul npow
#align function.surjective.semiring Function.Surjective.semiring

/-- Pushforward a `NonUnitalNonAssocRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalNonAssocRing β where
  toAddCommGroup := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
#align function.surjective.non_unital_non_assoc_ring Function.Surjective.nonUnitalNonAssocRing

/-- Pushforward a `NonUnitalRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalRing [NonUnitalRing α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul
#align function.surjective.non_unital_ring Function.Surjective.nonUnitalRing

/-- Pushforward a `NonAssocRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonAssocRing [NonAssocRing α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : NonAssocRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
#align function.surjective.non_assoc_ring Function.Surjective.nonAssocRing

/-- Pushforward a `Ring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev ring [Ring α] (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : Ring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
#align function.surjective.ring Function.Surjective.ring

/-- Pushforward a `NonUnitalNonAssocCommSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocCommSemiring  [NonUnitalNonAssocCommSemiring α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommSemiring β where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

/-- Pushforward a `NonUnitalCommSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalCommSemiring β where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul
#align function.surjective.non_unital_comm_semiring Function.Surjective.nonUnitalCommSemiring

/-- Pushforward a `CommSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev commSemiring [CommSemiring α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) : CommSemiring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.commSemigroup f mul
#align function.surjective.comm_semiring Function.Surjective.commSemiring

/-- Pushforward a `NonUnitalNonAssocCommRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing α]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommRing β where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

/-- Pushforward a `NonUnitalCommRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev nonUnitalCommRing [NonUnitalCommRing α] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalCommRing β where
  toNonUnitalRing := hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul
#align function.surjective.non_unital_comm_ring Function.Surjective.nonUnitalCommRing

/-- Pushforward a `CommRing` instance along a surjective function. -/
-- See note [reducible non-instances]
protected abbrev commRing [CommRing α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : CommRing β where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commMonoid f one mul npow
#align function.surjective.comm_ring Function.Surjective.commRing

end Function.Surjective

variable [Mul α] [HasDistribNeg α]

instance AddOpposite.instHasDistribNeg : HasDistribNeg αᵃᵒᵖ :=
  unop_injective.hasDistribNeg _ unop_neg unop_mul
