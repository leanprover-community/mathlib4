/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.Order.Ring.Defs

/-!
# Pulling back ordered rings along injective maps
-/

variable {R S : Type*}

namespace Function.Injective
variable [Semiring R] [PartialOrder R]
-- variable [Zero S] [One S] [Add S] [Mul S] [SMul ℕ S] [Pow S ℕ] [NatCast S]
-- variable (f : S → R) (hf : Injective f)

/-- Pullback an `IsOrderedRing` under an injective map. -/
protected lemma isOrderedRing [IsOrderedRing R] [Semiring S] [PartialOrder S]
    (f : S → R) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) :
    IsOrderedRing S :=
  { __ := Function.Injective.isOrderedAddMonoid f add le
    zero_le_one := le.1 <| by simp only [zero, one, zero_le_one]
    mul_le_mul_of_nonneg_left a b c h hc := le.1 <| by
      rw [mul, mul]; refine mul_le_mul_of_nonneg_left (le.2 h) ?_; rwa [← zero, le]
    mul_le_mul_of_nonneg_right a b c h hc := le.1 <| by
      rw [mul, mul]; refine mul_le_mul_of_nonneg_right (le.2 h) ?_; rwa [← zero, le] }

/-- Pullback a `IsStrictOrderedRing` under an injective map. -/
protected lemma isStrictOrderedRing [IsStrictOrderedRing R] [Semiring S] [PartialOrder S]
    (f : S → R) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) (lt : ∀ {x y}, f x < f y ↔ x < y) :
    IsStrictOrderedRing S :=
  { __ := Function.Injective.isOrderedCancelAddMonoid f add le
    __ := domain_nontrivial f zero one
    __ := Function.Injective.isOrderedRing f zero one add mul le
    mul_lt_mul_of_pos_left a b c h hc := lt.1 <| by
      simpa only [mul, zero] using mul_lt_mul_of_pos_left (lt.2 h) (by rwa [← zero, lt])
    mul_lt_mul_of_pos_right a b c h hc := lt.1 <| by
      simpa only [mul, zero] using mul_lt_mul_of_pos_right (lt.2 h) (by rwa [← zero, lt]) }

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
