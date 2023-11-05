/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.Order.Monoid.Cancel.Defs

#align_import algebra.order.monoid.cancel.basic from "leanprover-community/mathlib"@"f1a2caaf51ef593799107fe9a8d5e411599f3996"

/-!
# Basic results on ordered cancellative monoids.

We pull back ordered cancellative monoids along injective maps.
-/


universe u

variable {α : Type u}

open Function

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α]

/-- Pullback an `OrderedCancelCommMonoid` under an injective map.
See note [reducible non-instances]. -/
@[to_additive (attr := reducible) Function.Injective.orderedCancelAddCommMonoid
    "Pullback an `OrderedCancelAddCommMonoid` under an injective map."]
def Function.Injective.orderedCancelCommMonoid {β : Type*} [One β] [Mul β] [Pow β ℕ] (f : β → α)
    (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : OrderedCancelCommMonoid β :=
  { hf.orderedCommMonoid f one mul npow with
    le_of_mul_le_mul_left := fun a b c (bc : f (a * b) ≤ f (a * c)) ↦
      (mul_le_mul_iff_left (f a)).mp (by rwa [← mul, ← mul]) }
#align function.injective.ordered_cancel_comm_monoid Function.Injective.orderedCancelCommMonoid
#align function.injective.ordered_cancel_add_comm_monoid Function.Injective.orderedCancelAddCommMonoid

end OrderedCancelCommMonoid

section LinearOrderedCancelCommMonoid

variable [LinearOrderedCancelCommMonoid α]

/-- Pullback a `LinearOrderedCancelCommMonoid` under an injective map.
See note [reducible non-instances]. -/
@[to_additive (attr := reducible) Function.Injective.linearOrderedCancelAddCommMonoid
    "Pullback a `LinearOrderedCancelAddCommMonoid` under an injective map."]
def Function.Injective.linearOrderedCancelCommMonoid {β : Type*} [One β] [Mul β] [Pow β ℕ]
    [Sup β] [Inf β] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCancelCommMonoid β :=
  { hf.linearOrderedCommMonoid f one mul npow hsup hinf,
    hf.orderedCancelCommMonoid f one mul npow with }
#align function.injective.linear_ordered_cancel_comm_monoid Function.Injective.linearOrderedCancelCommMonoid
#align function.injective.linear_ordered_cancel_add_comm_monoid Function.Injective.linearOrderedCancelAddCommMonoid

end LinearOrderedCancelCommMonoid
