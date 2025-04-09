/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Group.InjSurj
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.InjSurj

/-!
# Pulling back ordered rings along injective maps
-/

open Function

variable {α β : Type*}

namespace Function.Injective

section

variable [Semiring α] [PartialOrder α]
  [Zero β] [One β] [Add β] [Mul β] [SMul ℕ β] [Pow β ℕ] [NatCast β] (f : β → α) (hf : Injective f)

/-- Pullback an `IsOrderedRing` under an injective map. -/
protected lemma isOrderedRing [IsOrderedRing α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) :
    letI _ : Semiring β := hf.semiring f zero one add mul nsmul npow natCast
    letI _ : PartialOrder β := PartialOrder.lift f hf
    IsOrderedRing β :=
  letI _ : Semiring β := hf.semiring f zero one add mul nsmul npow natCast
  letI _ : PartialOrder β := PartialOrder.lift f hf
  { __ := hf.isOrderedAddMonoid f zero add (swap nsmul)
    zero_le_one := show f 0 ≤ f 1 by simp only [zero, one, zero_le_one]
    mul_le_mul_of_nonneg_left a b c h hc := show f (c * a) ≤ f (c * b) by
      rw [mul, mul]; refine mul_le_mul_of_nonneg_left h ?_; rwa [← zero]
    mul_le_mul_of_nonneg_right a b c h hc := show f (a * c) ≤ f (b * c) by
      rw [mul, mul]; refine mul_le_mul_of_nonneg_right h ?_; rwa [← zero] }

/-- Pullback a `IsStrictOrderedRing` under an injective map. -/
protected lemma isStrictOrderedRing [IsStrictOrderedRing α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) :
    letI _ : Semiring β := hf.semiring f zero one add mul nsmul npow natCast
    letI _ : PartialOrder β := PartialOrder.lift f hf
    IsStrictOrderedRing β :=
  letI _ : Semiring β := hf.semiring f zero one add mul nsmul npow natCast
  letI _ : PartialOrder β := PartialOrder.lift f hf
  { __ := hf.isOrderedCancelAddMonoid f zero add (swap nsmul)
    __ := domain_nontrivial f zero one
    __ := hf.isOrderedRing f zero one add mul nsmul npow natCast
    mul_lt_mul_of_pos_left a b c h hc := show f (c * a) < f (c * b) by
      simpa only [mul, zero] using mul_lt_mul_of_pos_left ‹f a < f b› (by rwa [← zero])
    mul_lt_mul_of_pos_right a b c h hc := show f (a * c) < f (b * c) by
      simpa only [mul, zero] using mul_lt_mul_of_pos_right ‹f a < f b› (by rwa [← zero]) }

end

variable [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [SMul ℕ β] [SMul ℤ β] [Pow β ℕ]
  [NatCast β] [IntCast β] [Max β] [Min β] (f : β → α) (hf : Injective f)

/-- Pullback an `OrderedSemiring` under an injective map. -/
-- See note [reducible non-instances]
protected abbrev orderedSemiring [OrderedSemiring α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) : OrderedSemiring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.orderedAddCommMonoid f zero add (swap nsmul)
  zero_le_one := show f 0 ≤ f 1 by simp only [zero, one, zero_le_one]
  mul_le_mul_of_nonneg_left a b c h hc := show f (c * a) ≤ f (c * b) by
    rw [mul, mul]; refine mul_le_mul_of_nonneg_left h ?_; rwa [← zero]
  mul_le_mul_of_nonneg_right a b c h hc := show f (a * c) ≤ f (b * c) by
    rw [mul, mul]; refine mul_le_mul_of_nonneg_right h ?_; rwa [← zero]

/-- Pullback an `OrderedCommSemiring` under an injective map. -/
-- See note [reducible non-instances]
protected abbrev orderedCommSemiring [OrderedCommSemiring α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) : OrderedCommSemiring β where
  toOrderedSemiring := hf.orderedSemiring f zero one add mul nsmul npow natCast
  __ := hf.commSemiring f zero one add mul nsmul npow natCast

/-- Pullback an `OrderedRing` under an injective map. -/
-- See note [reducible non-instances]
protected abbrev orderedRing [OrderedRing α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : OrderedRing β where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.orderedAddCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.orderedSemiring f zero one add mul nsmul npow natCast
  mul_nonneg a b ha hb := show f 0 ≤ f (a * b) by rw [zero, mul]; apply mul_nonneg <;> rwa [← zero]

/-- Pullback an `OrderedCommRing` under an injective map. -/
-- See note [reducible non-instances]
protected abbrev orderedCommRing [OrderedCommRing α]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : OrderedCommRing β where
  toOrderedRing := hf.orderedRing f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commRing f zero one add mul neg sub nsmul zsmul npow natCast intCast

/-- Pullback a `StrictOrderedSemiring` under an injective map. -/
-- See note [reducible non-instances]
protected abbrev strictOrderedSemiring [StrictOrderedSemiring α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) : StrictOrderedSemiring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.orderedCancelAddCommMonoid f zero add (swap nsmul)
  __ := domain_nontrivial f zero one
  __ := hf.orderedSemiring f zero one add mul nsmul npow natCast
  mul_lt_mul_of_pos_left a b c h hc := show f (c * a) < f (c * b) by
    simpa only [mul, zero] using mul_lt_mul_of_pos_left ‹f a < f b› (by rwa [← zero])
  mul_lt_mul_of_pos_right a b c h hc := show f (a * c) < f (b * c) by
    simpa only [mul, zero] using mul_lt_mul_of_pos_right ‹f a < f b› (by rwa [← zero])

/-- Pullback a `strictOrderedCommSemiring` under an injective map. -/
-- See note [reducible non-instances]
protected abbrev strictOrderedCommSemiring [StrictOrderedCommSemiring α]
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) : StrictOrderedCommSemiring β where
  toStrictOrderedSemiring := hf.strictOrderedSemiring f zero one add mul nsmul npow natCast
  __ := hf.commSemiring f zero one add mul nsmul npow natCast

/-- Pullback a `StrictOrderedRing` under an injective map. -/
-- See note [reducible non-instances]
protected abbrev strictOrderedRing [StrictOrderedRing α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : StrictOrderedRing β where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.orderedAddCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.strictOrderedSemiring f zero one add mul nsmul npow natCast
  mul_pos a b ha hb := show f 0 < f (a * b) by rw [zero, mul]; apply mul_pos <;> rwa [← zero]

/-- Pullback a `StrictOrderedCommRing` under an injective map. -/
-- See note [reducible non-instances]
protected abbrev strictOrderedCommRing [StrictOrderedCommRing α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : StrictOrderedCommRing β where
  toStrictOrderedRing := hf.strictOrderedRing f zero one add mul neg sub nsmul zsmul npow natCast
    intCast
  __ := hf.commRing f zero one add mul neg sub nsmul zsmul npow natCast intCast

/-- Pullback a `LinearOrderedSemiring` under an injective map. -/
-- See note [reducible non-instances]
protected abbrev linearOrderedSemiring [LinearOrderedSemiring α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (sup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (inf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedSemiring β where
  toStrictOrderedSemiring := hf.strictOrderedSemiring f zero one add mul nsmul npow natCast
  __ := hf.linearOrderedAddCommMonoid f zero add (swap nsmul) sup inf

/-- Pullback a `LinearOrderedSemiring` under an injective map. -/
-- -- See note [reducible non-instances]
protected abbrev linearOrderedCommSemiring [LinearOrderedCommSemiring α]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommSemiring β where
  toStrictOrderedCommSemiring := hf.strictOrderedCommSemiring f zero one add mul nsmul npow natCast
  __ := hf.linearOrderedSemiring f zero one add mul nsmul npow natCast hsup hinf

/-- Pullback a `LinearOrderedRing` under an injective map. -/
-- See note [reducible non-instances]
abbrev linearOrderedRing [LinearOrderedRing α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedRing β where
  toStrictOrderedRing := hf.strictOrderedRing f zero one add mul neg sub nsmul zsmul npow natCast
    intCast
  __ := LinearOrder.lift f hf hsup hinf

/-- Pullback a `LinearOrderedCommRing` under an injective map. -/
-- See note [reducible non-instances]
protected abbrev linearOrderedCommRing [LinearOrderedCommRing α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) (sup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
    (inf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) : LinearOrderedCommRing β where
  toLinearOrderedRing := hf.linearOrderedRing f zero one add mul neg sub nsmul zsmul npow natCast
    intCast sup inf
  __ := hf.commMonoid f one mul npow

end Function.Injective
