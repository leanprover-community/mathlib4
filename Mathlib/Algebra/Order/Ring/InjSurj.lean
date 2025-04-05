/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.InjSurj

/-!
# Pulling back ordered rings along injective maps
-/

open Function

variable {α β : Type*}

namespace Function.Injective
variable [Semiring α] [PartialOrder α]
  [Zero β] [One β] [Add β] [Mul β] [SMul ℕ β] [Pow β ℕ] [NatCast β] (f : β → α) (hf : Injective f)

/-- Pullback an `IsOrderedRing` under an injective map. -/
protected lemma isOrderedRing [IsOrderedRing α] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) :
    let _ : Semiring β := hf.semiring f zero one add mul nsmul npow natCast
    let _ : PartialOrder β := PartialOrder.lift f hf
    IsOrderedRing β :=
  let _ : Semiring β := hf.semiring f zero one add mul nsmul npow natCast
  let _ : PartialOrder β := PartialOrder.lift f hf
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
    let _ : Semiring β := hf.semiring f zero one add mul nsmul npow natCast
    let _ : PartialOrder β := PartialOrder.lift f hf
    IsStrictOrderedRing β :=
  let _ : Semiring β := hf.semiring f zero one add mul nsmul npow natCast
  let _ : PartialOrder β := PartialOrder.lift f hf
  { __ := hf.isOrderedCancelAddMonoid f zero add (swap nsmul)
    __ := domain_nontrivial f zero one
    __ := hf.isOrderedRing f zero one add mul nsmul npow natCast
    mul_lt_mul_of_pos_left a b c h hc := show f (c * a) < f (c * b) by
      simpa only [mul, zero] using mul_lt_mul_of_pos_left ‹f a < f b› (by rwa [← zero])
    mul_lt_mul_of_pos_right a b c h hc := show f (a * c) < f (b * c) by
      simpa only [mul, zero] using mul_lt_mul_of_pos_right ‹f a < f b› (by rwa [← zero]) }

@[deprecated (since := "2025-01-06")]
protected alias orderedSemiring := Function.Injective.isOrderedRing
@[deprecated (since := "2025-01-06")]
protected alias orderedCommSemiring := Function.Injective.isOrderedRing
@[deprecated (since := "2025-01-06")]
protected alias orderedRing := Function.Injective.isOrderedRing
@[deprecated (since := "2025-01-06")]
protected alias orderedCommRing := Function.Injective.isOrderedRing
@[deprecated (since := "2025-01-06")]
protected alias strictOrderedSemiring := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-01-06")]
protected alias strictOrderedCommSemiring := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-01-06")]
protected alias strictOrderedRing := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-01-06")]
protected alias strictOrderedCommRing := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-01-06")]
protected alias linearOrderedSemiring := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-01-06")]
protected alias linearOrderedCommSemiring := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-01-06")]
protected alias linearOrderedRing := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-01-06")]
protected alias linearOrderedCommRing := Function.Injective.isStrictOrderedRing

end Function.Injective
