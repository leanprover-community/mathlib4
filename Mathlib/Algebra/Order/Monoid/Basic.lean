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
    OrderedCommMonoid β where
  toCommMonoid := hf.commMonoid f one mul npow
  toPartialOrder := PartialOrder.lift f hf
  mul_le_mul_left a b ab c := show f (c * a) ≤ f (c * b) by
    rw [mul, mul]; apply mul_le_mul_left'; exact ab
#align function.injective.ordered_comm_monoid Function.Injective.orderedCommMonoid
#align function.injective.ordered_add_comm_monoid Function.Injective.orderedAddCommMonoid

/-- Pullback an `OrderedCancelCommMonoid` under an injective map.
See note [reducible non-instances]. -/
@[to_additive (attr := reducible) Function.Injective.orderedCancelAddCommMonoid
    "Pullback an `OrderedCancelAddCommMonoid` under an injective map."]
def Function.Injective.orderedCancelCommMonoid [OrderedCancelCommMonoid α] [One β] [Mul β] [Pow β ℕ]
    (f : β → α) (hf : Injective f) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : OrderedCancelCommMonoid β where
  toOrderedCommMonoid := hf.orderedCommMonoid f one mul npow
  le_of_mul_le_mul_left a b c (bc : f (a * b) ≤ f (a * c)) :=
    (mul_le_mul_iff_left (f a)).1 (by rwa [← mul, ← mul])
#align function.injective.ordered_cancel_comm_monoid Function.Injective.orderedCancelCommMonoid
#align function.injective.ordered_cancel_add_comm_monoid Function.Injective.orderedCancelAddCommMonoid

/-- Pullback a `LinearOrderedCommMonoid` under an injective map.
See note [reducible non-instances]. -/
@[to_additive (attr := reducible) "Pullback an `OrderedAddCommMonoid` under an injective map."]
def Function.Injective.linearOrderedCommMonoid [LinearOrderedCommMonoid α] {β : Type*} [One β]
    [Mul β] [Pow β ℕ] [Sup β] [Inf β] (f : β → α) (hf : Function.Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (sup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (inf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommMonoid β where
  toOrderedCommMonoid := hf.orderedCommMonoid f one mul npow
  __ := LinearOrder.lift f hf sup inf
#align function.injective.linear_ordered_comm_monoid Function.Injective.linearOrderedCommMonoid
#align function.injective.linear_ordered_add_comm_monoid Function.Injective.linearOrderedAddCommMonoid

/-- Pullback a `LinearOrderedCancelCommMonoid` under an injective map.
See note [reducible non-instances]. -/
@[to_additive (attr := reducible) Function.Injective.linearOrderedCancelAddCommMonoid
    "Pullback a `LinearOrderedCancelAddCommMonoid` under an injective map."]
def Function.Injective.linearOrderedCancelCommMonoid [LinearOrderedCancelCommMonoid α] [One β]
    [Mul β] [Pow β ℕ] [Sup β] [Inf β] (f : β → α) (hf : Injective f) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCancelCommMonoid β where
  toOrderedCancelCommMonoid := hf.orderedCancelCommMonoid f one mul npow
  __ := hf.linearOrderedCommMonoid f one mul npow hsup hinf
#align function.injective.linear_ordered_cancel_comm_monoid Function.Injective.linearOrderedCancelCommMonoid
#align function.injective.linear_ordered_cancel_add_comm_monoid Function.Injective.linearOrderedCancelAddCommMonoid

-- TODO find a better home for the next two constructions.
/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `OrderIso.mulLeft` when working in an ordered group. -/
@[to_additive (attr := simps!)
      "The order embedding sending `b` to `a + b`, for some fixed `a`.
       See also `OrderIso.addLeft` when working in an additive ordered group."]
def OrderEmbedding.mulLeft {α : Type*} [Mul α] [LinearOrder α]
    [CovariantClass α α (· * ·) (· < ·)] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => m * n) fun _ _ w => mul_lt_mul_left' w m
#align order_embedding.mul_left OrderEmbedding.mulLeft
#align order_embedding.add_left OrderEmbedding.addLeft
#align order_embedding.mul_left_apply OrderEmbedding.mulLeft_apply
#align order_embedding.add_left_apply OrderEmbedding.addLeft_apply

/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `OrderIso.mulRight` when working in an ordered group. -/
@[to_additive (attr := simps!)
      "The order embedding sending `b` to `b + a`, for some fixed `a`.
       See also `OrderIso.addRight` when working in an additive ordered group."]
def OrderEmbedding.mulRight {α : Type*} [Mul α] [LinearOrder α]
    [CovariantClass α α (swap (· * ·)) (· < ·)] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => n * m) fun _ _ w => mul_lt_mul_right' w m
#align order_embedding.mul_right OrderEmbedding.mulRight
#align order_embedding.add_right OrderEmbedding.addRight
#align order_embedding.mul_right_apply OrderEmbedding.mulRight_apply
#align order_embedding.add_right_apply OrderEmbedding.addRight_apply
