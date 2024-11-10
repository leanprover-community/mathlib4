/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Basic

/-!
# Pull back ordered groups along injective maps.
-/


variable {α β : Type*}

/-- Pullback an `OrderedCommGroup` under an injective map.
See note [reducible non-instances]. -/
@[to_additive "Pullback an `OrderedAddCommGroup` under an injective map."]
abbrev Function.Injective.orderedCommGroup [OrderedCommGroup α] {β : Type*} [One β] [Mul β] [Inv β]
    [Div β] [Pow β ℕ] [Pow β ℤ] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : OrderedCommGroup β where
  toCommGroup := hf.commGroup f one mul inv div npow zpow
  toPartialOrder := PartialOrder.lift f hf
  __ := hf.orderedCommMonoid f one mul npow

/-- Pullback a `LinearOrderedCommGroup` under an injective map.
See note [reducible non-instances]. -/
@[to_additive "Pullback a `LinearOrderedAddCommGroup` under an injective map."]
abbrev Function.Injective.linearOrderedCommGroup [LinearOrderedCommGroup α] {β : Type*} [One β]
    [Mul β] [Inv β] [Div β] [Pow β ℕ] [Pow β ℤ] [Max β] [Min β] (f : β → α)
    (hf : Function.Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (sup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (inf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommGroup β where
  toOrderedCommGroup := hf.orderedCommGroup f one mul inv div npow zpow
  __ := LinearOrder.lift f hf sup inf
