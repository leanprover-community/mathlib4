/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Hom.Basic

#align_import algebra.order.monoid.basic from "leanprover-community/mathlib"@"9b2660e1b25419042c8da10bf411aa3c67f14383"

/-!
# Ordered monoids

This file develops some additional material on ordered monoids.
-/


open Function

universe u

variable {α : Type u} {β : Type*}

/-- Pullback an `OrderedCommMonoid` under an injective map.
See note [reducible non-instances]. -/
@[to_additive (attr := reducible) "Pullback an `OrderedAddCommMonoid` under an injective map."]
def Function.Injective.orderedCommMonoid [OrderedCommMonoid α] {β : Type*} [One β] [Mul β]
    [Pow β ℕ] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    OrderedCommMonoid β :=
  { PartialOrder.lift f hf,
    hf.commMonoid f one mul npow with
    mul_le_mul_left := fun a b ab c =>
      show f (c * a) ≤ f (c * b) by
        rw [mul, mul]
        apply mul_le_mul_left'
        exact ab }

/-- Pullback a `LinearOrderedCommMonoid` under an injective map.
See note [reducible non-instances]. -/
@[to_additive (attr := reducible) "Pullback an `OrderedAddCommMonoid` under an injective map."]
def Function.Injective.linearOrderedCommMonoid [LinearOrderedCommMonoid α] {β : Type*} [One β]
    [Mul β] [Pow β ℕ] [Sup β] [Inf β] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommMonoid β :=
  { hf.orderedCommMonoid f one mul npow, LinearOrder.lift f hf hsup hinf with }

-- TODO find a better home for the next two constructions.
/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `OrderIso.mulLeft` when working in an ordered group. -/
@[to_additive (attr := simps!)
      "The order embedding sending `b` to `a + b`, for some fixed `a`.
       See also `OrderIso.addLeft` when working in an additive ordered group."]
def OrderEmbedding.mulLeft {α : Type*} [Mul α] [LinearOrder α]
    [CovariantClass α α (· * ·) (· < ·)] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => m * n) fun _ _ w => mul_lt_mul_left' w m

/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `OrderIso.mulRight` when working in an ordered group. -/
@[to_additive (attr := simps!)
      "The order embedding sending `b` to `b + a`, for some fixed `a`.
       See also `OrderIso.addRight` when working in an additive ordered group."]
def OrderEmbedding.mulRight {α : Type*} [Mul α] [LinearOrder α]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => n * m) fun _ _ w => mul_lt_mul_right' w m
