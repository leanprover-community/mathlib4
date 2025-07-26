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

variable {R S : Type*}

namespace Function.Injective
variable [Semiring R] [PartialOrder R]
  [Zero S] [One S] [Add S] [Mul S] [SMul ℕ S] [Pow S ℕ] [NatCast S] (f : S → R) (hf : Injective f)

/-- Pullback an `IsOrderedRing` under an injective map. -/
protected lemma isOrderedRing [IsOrderedRing R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) :
    letI _ : Semiring S := hf.semiring f zero one add mul nsmul npow natCast
    letI _ : PartialOrder S := PartialOrder.lift f hf
    IsOrderedRing S :=
  letI _ : Semiring S := hf.semiring f zero one add mul nsmul npow natCast
  letI _ : PartialOrder S := PartialOrder.lift f hf
  { __ := hf.isOrderedAddMonoid f zero add (swap nsmul)
    zero_le_one := show f 0 ≤ f 1 by simp only [zero, one, zero_le_one]
    mul_le_mul_of_nonneg_left a b c h hc := show f (c * a) ≤ f (c * b) by
      rw [mul, mul]; refine mul_le_mul_of_nonneg_left h ?_; rwa [← zero]
    mul_le_mul_of_nonneg_right a b c h hc := show f (a * c) ≤ f (b * c) by
      rw [mul, mul]; refine mul_le_mul_of_nonneg_right h ?_; rwa [← zero] }

/-- Pullback a `IsStrictOrderedRing` under an injective map. -/
protected lemma isStrictOrderedRing [IsStrictOrderedRing R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) :
    letI _ : Semiring S := hf.semiring f zero one add mul nsmul npow natCast
    letI _ : PartialOrder S := PartialOrder.lift f hf
    IsStrictOrderedRing S :=
  letI _ : Semiring S := hf.semiring f zero one add mul nsmul npow natCast
  letI _ : PartialOrder S := PartialOrder.lift f hf
  { __ := hf.isOrderedCancelAddMonoid f zero add (swap nsmul)
    __ := domain_nontrivial f zero one
    __ := hf.isOrderedRing f zero one add mul nsmul npow natCast
    mul_lt_mul_of_pos_left a b c h hc := show f (c * a) < f (c * b) by
      simpa only [mul, zero] using mul_lt_mul_of_pos_left ‹f a < f b› (by rwa [← zero])
    mul_lt_mul_of_pos_right a b c h hc := show f (a * c) < f (b * c) by
      simpa only [mul, zero] using mul_lt_mul_of_pos_right ‹f a < f b› (by rwa [← zero]) }

@[deprecated (since := "2025-04-10")]
protected alias orderedSemiring := Function.Injective.isOrderedRing
@[deprecated (since := "2025-04-10")]
protected alias orderedCommSemiring := Function.Injective.isOrderedRing
@[deprecated (since := "2025-04-10")]
protected alias orderedRing := Function.Injective.isOrderedRing
@[deprecated (since := "2025-04-10")]
protected alias orderedCommRing := Function.Injective.isOrderedRing
@[deprecated (since := "2025-04-10")]
protected alias strictOrderedSemiring := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-04-10")]
protected alias strictOrderedCommSemiring := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-04-10")]
protected alias strictOrderedRing := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-04-10")]
protected alias strictOrderedCommRing := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-04-10")]
protected alias linearOrderedSemiring := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-04-10")]
protected alias linearOrderedCommSemiring := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-04-10")]
protected alias linearOrderedRing := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-04-10")]
protected alias linearOrderedCommRing := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-04-10")]
alias linearOrderedSemifield := Function.Injective.isStrictOrderedRing
@[deprecated (since := "2025-04-10")]
alias linearOrderedField := Function.Injective.isStrictOrderedRing

end Function.Injective
