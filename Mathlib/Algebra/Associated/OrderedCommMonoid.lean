/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import Mathlib.Algebra.Associated.Basic
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

#align_import algebra.associated from "leanprover-community/mathlib"@"2f3994e1b117b1e1da49bcfb67334f33460c3ce4"

/-!
# Associated, prime, and irreducible elements.

In this file we define the predicate `Prime p`
saying that an element of a commutative monoid with zero is prime.
Namely, `Prime p` means that `p` isn't zero, it isn't a unit,
and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`;

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Irreducible`,
however this is not true in general.

We also define an equivalence relation `Associated`
saying that two elements of a monoid differ by a multiplication by a unit.
Then we show that the quotient type `Associates` is a monoid
and prove basic properties of this quotient.
-/

variable {α : Type*} [CancelCommMonoidWithZero α]

namespace Associates

instance instOrderedCommMonoid : OrderedCommMonoid (Associates α) where
  mul_le_mul_left := fun a _ ⟨d, hd⟩ c => hd.symm ▸ mul_assoc c a d ▸ le_mul_right (α := α)

instance : CanonicallyOrderedCommMonoid (Associates α) where
  exists_mul_of_le h := h
  le_self_mul _ b := ⟨b, rfl⟩
  bot_le _ := one_le

end Associates
