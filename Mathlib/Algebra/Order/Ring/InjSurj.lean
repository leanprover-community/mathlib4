/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Group.InjSurj
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.InjSurj

#align_import algebra.order.ring.inj_surj from "leanprover-community/mathlib"@"655994e298904d7e5bbd1e18c95defd7b543eb94"

/-!
# Pulling back ordered rings along injective maps.

-/


open Function

universe u

variable {α : Type u} {β : Type*}

namespace Function.Injective

-- See note [reducible non-instances]
/-- Pullback an `OrderedSemiring` under an injective map. -/
@[reducible]
protected def orderedSemiring [OrderedSemiring α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ]
    [SMul ℕ β] [NatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : OrderedSemiring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow nat_cast
  __ := hf.orderedAddCommMonoid f zero add nsmul
  zero_le_one := show f 0 ≤ f 1 by simp only [zero, one, zero_le_one]
  mul_le_mul_of_nonneg_left a b c h hc := show f (c * a) ≤ f (c * b) by
    rw [mul, mul]; refine mul_le_mul_of_nonneg_left h ?_; rwa [← zero]
  mul_le_mul_of_nonneg_right a b c h hc := show f (a * c) ≤ f (b * c) by
    rw [mul, mul]; refine mul_le_mul_of_nonneg_right h ?_; rwa [← zero]
#align function.injective.ordered_semiring Function.Injective.orderedSemiring

-- See note [reducible non-instances]
/-- Pullback an `OrderedCommSemiring` under an injective map. -/
@[reducible]
protected def orderedCommSemiring [OrderedCommSemiring α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ]
    [SMul ℕ β] [NatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : OrderedCommSemiring β where
  toOrderedSemiring := hf.orderedSemiring f zero one add mul nsmul npow nat_cast
  __ := hf.commSemiring f zero one add mul nsmul npow nat_cast
#align function.injective.ordered_comm_semiring Function.Injective.orderedCommSemiring

-- See note [reducible non-instances]
/-- Pullback an `OrderedRing` under an injective map. -/
@[reducible]
protected def orderedRing [OrderedRing α] [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β]
    [SMul ℕ β] [SMul ℤ β] [Pow β ℕ] [NatCast β] [IntCast β] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : OrderedRing β where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast
  __ := hf.orderedAddCommGroup f zero add neg sub nsmul zsmul
  __ := hf.orderedSemiring f zero one add mul nsmul npow nat_cast
  mul_nonneg a b ha hb := show f 0 ≤ f (a * b) by rw [zero, mul]; apply mul_nonneg <;> rwa [← zero]
#align function.injective.ordered_ring Function.Injective.orderedRing

-- See note [reducible non-instances]
/-- Pullback an `OrderedCommRing` under an injective map. -/
@[reducible]
protected def orderedCommRing [OrderedCommRing α] [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β]
    [Pow β ℕ] [SMul ℕ β] [SMul ℤ β] [NatCast β] [IntCast β] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : OrderedCommRing β where
  toOrderedRing := hf.orderedRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast
  __ := hf.commRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast
#align function.injective.ordered_comm_ring Function.Injective.orderedCommRing

-- See note [reducible non-instances]
/-- Pullback a `StrictOrderedSemiring` under an injective map. -/
@[reducible]
protected def strictOrderedSemiring [StrictOrderedSemiring α] [Zero β] [One β] [Add β] [Mul β]
    [Pow β ℕ] [SMul ℕ β] [NatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : StrictOrderedSemiring β where
  toSemiring := hf.semiring f zero one add mul nsmul npow nat_cast
  __ := hf.orderedCancelAddCommMonoid f zero add nsmul
  __ := pullback_nonzero f zero one
  __ := hf.orderedSemiring f zero one add mul nsmul npow nat_cast
  mul_lt_mul_of_pos_left a b c h hc := show f (c * a) < f (c * b) by
    simpa only [mul, zero] using mul_lt_mul_of_pos_left ‹f a < f b› (by rwa [← zero])
  mul_lt_mul_of_pos_right a b c h hc := show f (a * c) < f (b * c) by
    simpa only [mul, zero] using mul_lt_mul_of_pos_right ‹f a < f b› (by rwa [← zero])
#align function.injective.strict_ordered_semiring Function.Injective.strictOrderedSemiring

-- See note [reducible non-instances]
/-- Pullback a `strictOrderedCommSemiring` under an injective map. -/
@[reducible]
protected def strictOrderedCommSemiring [StrictOrderedCommSemiring α] [Zero β] [One β] [Add β]
    [Mul β] [Pow β ℕ] [SMul ℕ β] [NatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : StrictOrderedCommSemiring β where
  toStrictOrderedSemiring := hf.strictOrderedSemiring f zero one add mul nsmul npow nat_cast
  __ := hf.commSemiring f zero one add mul nsmul npow nat_cast
#align function.injective.strict_ordered_comm_semiring Function.Injective.strictOrderedCommSemiring

-- See note [reducible non-instances]
/-- Pullback a `StrictOrderedRing` under an injective map. -/
@[reducible]
protected def strictOrderedRing [StrictOrderedRing α] [Zero β] [One β] [Add β] [Mul β] [Neg β]
    [Sub β] [SMul ℕ β] [SMul ℤ β] [Pow β ℕ] [NatCast β] [IntCast β] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : StrictOrderedRing β where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast
  __ := hf.orderedAddCommGroup f zero add neg sub nsmul zsmul
  __ := hf.strictOrderedSemiring f zero one add mul nsmul npow nat_cast
  mul_pos a b ha hb := show f 0 < f (a * b) by rw [zero, mul]; apply mul_pos <;> rwa [← zero]
#align function.injective.strict_ordered_ring Function.Injective.strictOrderedRing

-- See note [reducible non-instances]
/-- Pullback a `StrictOrderedCommRing` under an injective map. -/
@[reducible]
protected def strictOrderedCommRing [StrictOrderedCommRing α] [Zero β] [One β] [Add β] [Mul β]
    [Neg β] [Sub β] [Pow β ℕ] [SMul ℕ β] [SMul ℤ β] [NatCast β] [IntCast β] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : StrictOrderedCommRing β where
  toStrictOrderedRing := hf.strictOrderedRing f zero one add mul neg sub nsmul zsmul npow nat_cast
    int_cast
  __ := hf.commRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast
#align function.injective.strict_ordered_comm_ring Function.Injective.strictOrderedCommRing

-- See note [reducible non-instances]
/-- Pullback a `LinearOrderedSemiring` under an injective map. -/
@[reducible]
protected def linearOrderedSemiring [LinearOrderedSemiring α] [Zero β] [One β] [Add β] [Mul β]
    [Pow β ℕ] [SMul ℕ β] [NatCast β] [Sup β] [Inf β] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n)
    (sup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (inf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedSemiring β where
  toStrictOrderedSemiring := hf.strictOrderedSemiring f zero one add mul nsmul npow nat_cast
  __ := hf.linearOrderedAddCommMonoid f zero add nsmul sup inf
#align function.injective.linear_ordered_semiring Function.Injective.linearOrderedSemiring

-- See note [reducible non-instances]
/-- Pullback a `LinearOrderedSemiring` under an injective map. -/
@[reducible]
protected def linearOrderedCommSemiring [LinearOrderedCommSemiring α] [Zero β] [One β] [Add β]
    [Mul β] [Pow β ℕ] [SMul ℕ β] [NatCast β] [Sup β] [Inf β] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommSemiring β where
  toStrictOrderedCommSemiring := hf.strictOrderedCommSemiring f zero one add mul nsmul npow nat_cast
  __ := hf.linearOrderedSemiring f zero one add mul nsmul npow nat_cast hsup hinf
#align function.injective.linear_ordered_comm_semiring Function.Injective.linearOrderedCommSemiring

-- See note [reducible non-instances]
/-- Pullback a `LinearOrderedRing` under an injective map. -/
@[reducible]
def linearOrderedRing [LinearOrderedRing α] [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β]
    [SMul ℕ β] [SMul ℤ β] [Pow β ℕ] [NatCast β] [IntCast β] [Sup β] [Inf β] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedRing β where
  toStrictOrderedRing := hf.strictOrderedRing f zero one add mul neg sub nsmul zsmul npow nat_cast
    int_cast
  __ := LinearOrder.lift f hf hsup hinf
#align function.injective.linear_ordered_ring Function.Injective.linearOrderedRing

-- See note [reducible non-instances]
/-- Pullback a `LinearOrderedCommRing` under an injective map. -/
@[reducible]
protected def linearOrderedCommRing [LinearOrderedCommRing α] [Zero β] [One β] [Add β] [Mul β]
    [Neg β] [Sub β] [Pow β ℕ] [SMul ℕ β] [SMul ℤ β] [NatCast β] [IntCast β] [Sup β]
    [Inf β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) (sup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
    (inf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) : LinearOrderedCommRing β where
  toLinearOrderedRing := hf.linearOrderedRing f zero one add mul neg sub nsmul zsmul npow nat_cast
    int_cast sup inf
  __ := hf.commMonoid f one mul npow
#align function.injective.linear_ordered_comm_ring Function.Injective.linearOrderedCommRing

end Function.Injective
