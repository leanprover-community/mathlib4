/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathbin.Algebra.Ring.Defs
import Mathbin.Algebra.Opposites
import Mathbin.Algebra.GroupWithZero.InjSurj

/-!
# Pulling back rings along injective maps, and pushing them forward along surjective maps.

-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

/-!
### `distrib` class
-/


/-- Pullback a `distrib` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.distrib {S} [Mul R] [Add R] [Distrib S] (f : R → S) (hf : Injective f)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) : Distrib R where
  mul := (· * ·)
  add := (· + ·)
  left_distrib x y z := hf <| by simp only [*, left_distrib]
  right_distrib x y z := hf <| by simp only [*, right_distrib]
#align function.injective.distrib Function.Injective.distrib

/-- Pushforward a `distrib` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.distrib {S} [Distrib R] [Add S] [Mul S] (f : R → S) (hf : Surjective f)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) : Distrib S where
  mul := (· * ·)
  add := (· + ·)
  left_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, left_distrib]
  right_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, right_distrib]
#align function.surjective.distrib Function.Surjective.distrib

section InjectiveSurjectiveMaps

/-!
### Semirings
-/


variable [Zero β] [Add β] [Mul β] [HasSmul ℕ β]

/-- Pullback a `non_unital_non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalNonAssocSemiring {α : Type u} [NonUnitalNonAssocSemiring α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalNonAssocSemiring β :=
  { hf.MulZeroClass f zero mul, hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }
#align function.injective.non_unital_non_assoc_semiring Function.Injective.nonUnitalNonAssocSemiring

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalSemiring {α : Type u} [NonUnitalSemiring α] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalSemiring β :=
  { hf.NonUnitalNonAssocSemiring f zero add mul nsmul, hf.SemigroupWithZero f zero mul with }
#align function.injective.non_unital_semiring Function.Injective.nonUnitalSemiring

/-- Pullback a `non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonAssocSemiring {α : Type u} [NonAssocSemiring α] {β : Type v} [Zero β] [One β]
    [Mul β] [Add β] [HasSmul ℕ β] [NatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n) : NonAssocSemiring β :=
  { hf.AddMonoidWithOne f zero one add nsmul nat_cast, hf.NonUnitalNonAssocSemiring f zero add mul nsmul,
    hf.MulOneClass f one mul with }
#align function.injective.non_assoc_semiring Function.Injective.nonAssocSemiring

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.semiring {α : Type u} [Semiring α] {β : Type v} [Zero β] [One β] [Add β] [Mul β]
    [Pow β ℕ] [HasSmul ℕ β] [NatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : Semiring β :=
  { hf.NonAssocSemiring f zero one add mul nsmul nat_cast, hf.MonoidWithZero f zero one mul npow,
    hf.Distrib f add mul with }
#align function.injective.semiring Function.Injective.semiring

/-- Pushforward a `non_unital_non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalNonAssocSemiring {α : Type u} [NonUnitalNonAssocSemiring α] (f : α → β)
    (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalNonAssocSemiring β :=
  { hf.MulZeroClass f zero mul, hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }
#align function.surjective.non_unital_non_assoc_semiring Function.Surjective.nonUnitalNonAssocSemiring

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalSemiring {α : Type u} [NonUnitalSemiring α] (f : α → β) (hf : Surjective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalSemiring β :=
  { hf.NonUnitalNonAssocSemiring f zero add mul nsmul, hf.SemigroupWithZero f zero mul with }
#align function.surjective.non_unital_semiring Function.Surjective.nonUnitalSemiring

/-- Pushforward a `non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonAssocSemiring {α : Type u} [NonAssocSemiring α] {β : Type v} [Zero β] [One β]
    [Add β] [Mul β] [HasSmul ℕ β] [NatCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n) : NonAssocSemiring β :=
  { hf.AddMonoidWithOne f zero one add nsmul nat_cast, hf.NonUnitalNonAssocSemiring f zero add mul nsmul,
    hf.MulOneClass f one mul with }
#align function.surjective.non_assoc_semiring Function.Surjective.nonAssocSemiring

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.semiring {α : Type u} [Semiring α] {β : Type v} [Zero β] [One β] [Add β] [Mul β]
    [Pow β ℕ] [HasSmul ℕ β] [NatCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : Semiring β :=
  { hf.NonAssocSemiring f zero one add mul nsmul nat_cast, hf.MonoidWithZero f zero one mul npow,
    hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }
#align function.surjective.semiring Function.Surjective.semiring

end InjectiveSurjectiveMaps

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α] [NonUnitalCommSemiring β] {a b c : α}

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalCommSemiring [Zero γ] [Add γ] [Mul γ] [HasSmul ℕ γ] (f : γ → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalCommSemiring γ :=
  { hf.NonUnitalSemiring f zero add mul nsmul, hf.CommSemigroup f mul with }
#align function.injective.non_unital_comm_semiring Function.Injective.nonUnitalCommSemiring

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalCommSemiring [Zero γ] [Add γ] [Mul γ] [HasSmul ℕ γ] (f : α → γ)
    (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalCommSemiring γ :=
  { hf.NonUnitalSemiring f zero add mul nsmul, hf.CommSemigroup f mul with }
#align function.surjective.non_unital_comm_semiring Function.Surjective.nonUnitalCommSemiring

end NonUnitalCommSemiring

section CommSemiring

variable [CommSemiring α] [CommSemiring β] {a b c : α}

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commSemiring [Zero γ] [One γ] [Add γ] [Mul γ] [HasSmul ℕ γ] [NatCast γ] [Pow γ ℕ]
    (f : γ → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) : CommSemiring γ :=
  { hf.Semiring f zero one add mul nsmul npow nat_cast, hf.CommSemigroup f mul with }
#align function.injective.comm_semiring Function.Injective.commSemiring

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commSemiring [Zero γ] [One γ] [Add γ] [Mul γ] [HasSmul ℕ γ] [NatCast γ] [Pow γ ℕ]
    (f : α → γ) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) : CommSemiring γ :=
  { hf.Semiring f zero one add mul nsmul npow nat_cast, hf.CommSemigroup f mul with }
#align function.surjective.comm_semiring Function.Surjective.commSemiring

end CommSemiring

section HasDistribNeg

section Mul

variable [Mul α] [HasDistribNeg α]

-- See note [reducible non-instances]
/-- A type endowed with `-` and `*` has distributive negation, if it admits an injective map that
preserves `-` and `*` to a type which has distributive negation. -/
@[reducible]
protected def Function.Injective.hasDistribNeg [Neg β] [Mul β] (f : β → α) (hf : Injective f) (neg : ∀ a, f (-a) = -f a)
    (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg β :=
  { hf.HasInvolutiveNeg _ neg, ‹Mul β› with neg_mul := fun x y => hf <| by erw [neg, mul, neg, neg_mul, mul],
    mul_neg := fun x y => hf <| by erw [neg, mul, neg, mul_neg, mul] }
#align function.injective.has_distrib_neg Function.Injective.hasDistribNeg

-- See note [reducible non-instances]
/-- A type endowed with `-` and `*` has distributive negation, if it admits a surjective map that
preserves `-` and `*` from a type which has distributive negation. -/
@[reducible]
protected def Function.Surjective.hasDistribNeg [Neg β] [Mul β] (f : α → β) (hf : Surjective f)
    (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg β :=
  { hf.HasInvolutiveNeg _ neg, ‹Mul β› with
    neg_mul :=
      hf.Forall₂.2 fun x y => by
        erw [← neg, ← mul, neg_mul, neg, mul]
        rfl,
    mul_neg :=
      hf.Forall₂.2 fun x y => by
        erw [← neg, ← mul, mul_neg, neg, mul]
        rfl }
#align function.surjective.has_distrib_neg Function.Surjective.hasDistribNeg

namespace AddOpposite

instance : HasDistribNeg αᵃᵒᵖ :=
  unop_injective.HasDistribNeg _ unop_neg unop_mul

end AddOpposite

end Mul

end HasDistribNeg

/-!
### Rings
-/


section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/-- Pullback a `non_unital_non_assoc_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalNonAssocRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) :
    NonUnitalNonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul with }
#align function.injective.non_unital_non_assoc_ring Function.Injective.nonUnitalNonAssocRing

/-- Pushforward a `non_unital_non_assoc_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalNonAssocRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) :
    NonUnitalNonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul with }
#align function.surjective.non_unital_non_assoc_ring Function.Surjective.nonUnitalNonAssocRing

end NonUnitalNonAssocRing

section NonUnitalRing

variable [NonUnitalRing α]

/-- Pullback a `non_unital_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul,
    hf.Semigroup f mul with }
#align function.injective.non_unital_ring Function.Injective.nonUnitalRing

/-- Pushforward a `non_unital_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul,
    hf.Semigroup f mul with }
#align function.surjective.non_unital_ring Function.Surjective.nonUnitalRing

end NonUnitalRing

section NonAssocRing

variable [NonAssocRing α]

/-- Pullback a `non_assoc_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonAssocRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] [NatCast β] [IntCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (gsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
    NonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul,
    hf.AddGroupWithOne f zero one add neg sub nsmul gsmul nat_cast int_cast, hf.MulZeroClass f zero mul,
    hf.Distrib f add mul, hf.MulOneClass f one mul with }
#align function.injective.non_assoc_ring Function.Injective.nonAssocRing

/-- Pushforward a `non_unital_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonAssocRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] [NatCast β] [IntCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (gsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
    NonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul,
    hf.AddGroupWithOne f zero one add neg sub nsmul gsmul nat_cast int_cast, hf.Distrib f add mul,
    hf.MulOneClass f one mul with }
#align function.surjective.non_assoc_ring Function.Surjective.nonAssocRing

end NonAssocRing

section Ring

variable [Ring α] {a b c d e : α}

/-- Pullback a `ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.ring [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    [Pow β ℕ] [NatCast β] [IntCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : Ring β :=
  { hf.AddGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast,
    hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.Monoid f one mul npow, hf.Distrib f add mul with }
#align function.injective.ring Function.Injective.ring

/-- Pushforward a `ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.ring [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    [Pow β ℕ] [NatCast β] [IntCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : Ring β :=
  { hf.AddGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast,
    hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.Monoid f one mul npow, hf.Distrib f add mul with }
#align function.surjective.ring Function.Surjective.ring

end Ring

section NonUnitalCommRing

variable [NonUnitalCommRing α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalCommRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalCommRing β :=
  { hf.NonUnitalRing f zero add mul neg sub nsmul zsmul, hf.CommSemigroup f mul with }
#align function.injective.non_unital_comm_ring Function.Injective.nonUnitalCommRing

/-- Pushforward a `non_unital_comm_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalCommRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalCommRing β :=
  { hf.NonUnitalRing f zero add mul neg sub nsmul zsmul, hf.CommSemigroup f mul with }
#align function.surjective.non_unital_comm_ring Function.Surjective.nonUnitalCommRing

end NonUnitalCommRing

section CommRing

variable [CommRing α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    [Pow β ℕ] [NatCast β] [IntCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : CommRing β :=
  { hf.Ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast, hf.CommSemigroup f mul with }
#align function.injective.comm_ring Function.Injective.commRing

/-- Pushforward a `comm_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    [Pow β ℕ] [NatCast β] [IntCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : CommRing β :=
  { hf.Ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast, hf.CommSemigroup f mul with }
#align function.surjective.comm_ring Function.Surjective.commRing

end CommRing

