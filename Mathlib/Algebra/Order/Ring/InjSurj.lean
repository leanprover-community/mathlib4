/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathbin.Algebra.Order.Ring.Defs
import Mathbin.Algebra.Order.Monoid.Cancel.Basic
import Mathbin.Algebra.Ring.InjSurj

/-!
# Pulling back ordered rings along injective maps.

-/


open Function

universe u

variable {α : Type u} {β : Type _}

namespace Function.Injective

-- See note [reducible non-instances]
/-- Pullback an `ordered_semiring` under an injective map. -/
@[reducible]
protected def orderedSemiring [OrderedSemiring α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ]
    [HasSmul ℕ β] [NatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : OrderedSemiring β :=
  { hf.OrderedAddCommMonoid f zero add nsmul,
    hf.Semiring f zero one add mul nsmul npow nat_cast with
    zero_le_one := show f 0 ≤ f 1 by simp only [zero, one, zero_le_one],
    mul_le_mul_of_nonneg_left := fun a b c h hc =>
      show f (c * a) ≤ f (c * b) by
        rw [mul, mul]
        refine' mul_le_mul_of_nonneg_left h _
        rwa [← zero],
    mul_le_mul_of_nonneg_right := fun a b c h hc =>
      show f (a * c) ≤ f (b * c) by
        rw [mul, mul]
        refine' mul_le_mul_of_nonneg_right h _
        rwa [← zero] }
#align function.injective.ordered_semiring Function.Injective.orderedSemiring

-- See note [reducible non-instances]
/-- Pullback an `ordered_comm_semiring` under an injective map. -/
@[reducible]
protected def orderedCommSemiring [OrderedCommSemiring α] [Zero β] [One β] [Add β] [Mul β] [Pow β ℕ]
    [HasSmul ℕ β] [NatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : OrderedCommSemiring β :=
  { hf.CommSemiring f zero one add mul nsmul npow nat_cast,
    hf.OrderedSemiring f zero one add mul nsmul npow nat_cast with }
#align function.injective.ordered_comm_semiring Function.Injective.orderedCommSemiring

-- See note [reducible non-instances]
/-- Pullback an `ordered_ring` under an injective map. -/
@[reducible]
protected def orderedRing [OrderedRing α] [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β]
    [HasSmul ℕ β] [HasSmul ℤ β] [Pow β ℕ] [NatCast β] [IntCast β] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : OrderedRing β :=
  { hf.OrderedSemiring f zero one add mul nsmul npow nat_cast,
    hf.Ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with
    mul_nonneg := fun a b ha hb =>
      show f 0 ≤ f (a * b) by
        rw [zero, mul]
        apply mul_nonneg <;> rwa [← zero] }
#align function.injective.ordered_ring Function.Injective.orderedRing

-- See note [reducible non-instances]
/-- Pullback an `ordered_comm_ring` under an injective map. -/
@[reducible]
protected def orderedCommRing [OrderedCommRing α] [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β]
    [Pow β ℕ] [HasSmul ℕ β] [HasSmul ℤ β] [NatCast β] [IntCast β] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : OrderedCommRing β :=
  { hf.OrderedRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast,
    hf.CommRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with }
#align function.injective.ordered_comm_ring Function.Injective.orderedCommRing

-- See note [reducible non-instances]
/-- Pullback a `strict_ordered_semiring` under an injective map. -/
@[reducible]
protected def strictOrderedSemiring [StrictOrderedSemiring α] [Zero β] [One β] [Add β] [Mul β]
    [Pow β ℕ] [HasSmul ℕ β] [NatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : StrictOrderedSemiring β :=
  { hf.OrderedCancelAddCommMonoid f zero add nsmul,
    hf.OrderedSemiring f zero one add mul nsmul npow nat_cast, pullback_nonzero f zero one with
    mul_lt_mul_of_pos_left := fun a b c h hc =>
      show f (c * a) < f (c * b) by
        simpa only [mul, zero] using mul_lt_mul_of_pos_left ‹f a < f b› (by rwa [← zero]),
    mul_lt_mul_of_pos_right := fun a b c h hc =>
      show f (a * c) < f (b * c) by
        simpa only [mul, zero] using mul_lt_mul_of_pos_right ‹f a < f b› (by rwa [← zero]) }
#align function.injective.strict_ordered_semiring Function.Injective.strictOrderedSemiring

-- See note [reducible non-instances]
/-- Pullback a `strict_ordered_comm_semiring` under an injective map. -/
@[reducible]
protected def strictOrderedCommSemiring [StrictOrderedCommSemiring α] [Zero β] [One β] [Add β]
    [Mul β] [Pow β ℕ] [HasSmul ℕ β] [NatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : StrictOrderedCommSemiring β :=
  { hf.CommSemiring f zero one add mul nsmul npow nat_cast,
    hf.StrictOrderedSemiring f zero one add mul nsmul npow nat_cast with }
#align function.injective.strict_ordered_comm_semiring Function.Injective.strictOrderedCommSemiring

-- See note [reducible non-instances]
/-- Pullback a `strict_ordered_ring` under an injective map. -/
@[reducible]
protected def strictOrderedRing [StrictOrderedRing α] [Zero β] [One β] [Add β] [Mul β] [Neg β]
    [Sub β] [HasSmul ℕ β] [HasSmul ℤ β] [Pow β ℕ] [NatCast β] [IntCast β] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : StrictOrderedRing β :=
  { hf.StrictOrderedSemiring f zero one add mul nsmul npow nat_cast,
    hf.Ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with
    mul_pos := fun a b a0 b0 =>
      show f 0 < f (a * b) by
        rw [zero, mul]
        apply mul_pos <;> rwa [← zero] }
#align function.injective.strict_ordered_ring Function.Injective.strictOrderedRing

-- See note [reducible non-instances]
/-- Pullback a `strict_ordered_comm_ring` under an injective map. -/
@[reducible]
protected def strictOrderedCommRing [StrictOrderedCommRing α] [Zero β] [One β] [Add β] [Mul β]
    [Neg β] [Sub β] [Pow β ℕ] [HasSmul ℕ β] [HasSmul ℤ β] [NatCast β] [IntCast β] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : StrictOrderedCommRing β :=
  { hf.StrictOrderedRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast,
    hf.CommRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with }
#align function.injective.strict_ordered_comm_ring Function.Injective.strictOrderedCommRing

-- See note [reducible non-instances]
/-- Pullback a `linear_ordered_semiring` under an injective map. -/
@[reducible]
protected def linearOrderedSemiring [LinearOrderedSemiring α] [Zero β] [One β] [Add β] [Mul β]
    [Pow β ℕ] [HasSmul ℕ β] [NatCast β] [HasSup β] [HasInf β] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedSemiring β :=
  { LinearOrder.lift f hf hsup hinf,
    hf.StrictOrderedSemiring f zero one add mul nsmul npow nat_cast with }
#align function.injective.linear_ordered_semiring Function.Injective.linearOrderedSemiring

-- See note [reducible non-instances]
/-- Pullback a `linear_ordered_semiring` under an injective map. -/
@[reducible]
protected def linearOrderedCommSemiring [LinearOrderedCommSemiring α] [Zero β] [One β] [Add β]
    [Mul β] [Pow β ℕ] [HasSmul ℕ β] [NatCast β] [HasSup β] [HasInf β] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommSemiring β :=
  { hf.LinearOrderedSemiring f zero one add mul nsmul npow nat_cast hsup hinf,
    hf.StrictOrderedCommSemiring f zero one add mul nsmul npow nat_cast with }
#align function.injective.linear_ordered_comm_semiring Function.Injective.linearOrderedCommSemiring

-- See note [reducible non-instances]
/-- Pullback a `linear_ordered_ring` under an injective map. -/
@[reducible]
def linearOrderedRing [LinearOrderedRing α] [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β]
    [HasSmul ℕ β] [HasSmul ℤ β] [Pow β ℕ] [NatCast β] [IntCast β] [HasSup β] [HasInf β] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedRing β :=
  { LinearOrder.lift f hf hsup hinf,
    hf.StrictOrderedRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with }
#align function.injective.linear_ordered_ring Function.Injective.linearOrderedRing

-- See note [reducible non-instances]
/-- Pullback a `linear_ordered_comm_ring` under an injective map. -/
@[reducible]
protected def linearOrderedCommRing [LinearOrderedCommRing α] [Zero β] [One β] [Add β] [Mul β]
    [Neg β] [Sub β] [Pow β ℕ] [HasSmul ℕ β] [HasSmul ℤ β] [NatCast β] [IntCast β] [HasSup β]
    [HasInf β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n)
    (int_cast : ∀ n : ℤ, f n = n) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
    (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) : LinearOrderedCommRing β :=
  { LinearOrder.lift f hf hsup hinf,
    hf.StrictOrderedCommRing f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast with }
#align function.injective.linear_ordered_comm_ring Function.Injective.linearOrderedCommRing

end Function.Injective
