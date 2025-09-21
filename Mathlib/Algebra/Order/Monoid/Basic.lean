/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Order.Hom.Basic

/-!
# Ordered monoids

This file develops some additional material on ordered monoids.
-/


open Function

universe u

variable {α : Type u} {β : Type*} [CommMonoid α] [PartialOrder α]

/-- Pullback an `IsOrderedMonoid` under an injective map. -/
@[to_additive /-- Pullback an `IsOrderedAddMonoid` under an injective map. -/]
lemma Function.Injective.isOrderedMonoid [IsOrderedMonoid α] [CommMonoid β]
    [PartialOrder β] (f : β → α) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) :
    IsOrderedMonoid β where
  mul_le_mul_left a b ab c := le.1 <| by
      rw [mul, mul]; apply mul_le_mul_left'; exact le.2 ab

/-- Pullback an `IsOrderedMonoid` under a strictly monotone map. -/
@[to_additive /-- Pullback an `IsOrderedAddMonoid` under a strictly monotone map. -/]
lemma StrictMono.isOrderedMonoid [IsOrderedMonoid α] [CommMonoid β] [LinearOrder β]
    (f : β → α) (hf : StrictMono f) (mul : ∀ x y, f (x * y) = f x * f y) :
    IsOrderedMonoid β :=
  Function.Injective.isOrderedMonoid f mul hf.le_iff_le

/-- Pullback an `IsOrderedCancelMonoid` under an injective map. -/
@[to_additive Function.Injective.isOrderedCancelAddMonoid
    /-- Pullback an `IsOrderedCancelAddMonoid` under an injective map. -/]
lemma Function.Injective.isOrderedCancelMonoid [IsOrderedCancelMonoid α] [CommMonoid β]
    [PartialOrder β]
    (f : β → α) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) :
    IsOrderedCancelMonoid β where
  __ := Function.Injective.isOrderedMonoid f mul le
  le_of_mul_le_mul_left a b c bc := le.1 <|
      (mul_le_mul_iff_left (f a)).1 (by rwa [← mul, ← mul, le])

/-- Pullback an `IsOrderedCancelMonoid` under a strictly monotone map. -/
@[to_additive /-- Pullback an `IsOrderedAddCancelMonoid` under a strictly monotone map. -/]
lemma StrictMono.isOrderedCancelMonoid [IsOrderedCancelMonoid α] [CommMonoid β] [LinearOrder β]
    (f : β → α) (hf : StrictMono f) (mul : ∀ x y, f (x * y) = f x * f y) :
    IsOrderedCancelMonoid β where
  __ := hf.isOrderedMonoid f mul
  le_of_mul_le_mul_left a b c h := by simpa [← hf.le_iff_le, mul] using h

@[deprecated (since := "2025-04-10")]
alias Function.Injective.orderedCommMonoid := Function.Injective.isOrderedMonoid
@[deprecated (since := "2025-04-10")]
alias Function.Injective.orderedAddCommMonoid := Function.Injective.isOrderedAddMonoid
@[deprecated (since := "2025-04-10")]
alias Function.Injective.orderedCancelCommMonoid := Function.Injective.isOrderedCancelMonoid
@[deprecated (since := "2025-04-10")]
alias Function.Injective.orderedCancelAddCommMonoid := Function.Injective.isOrderedCancelAddMonoid
@[deprecated (since := "2025-04-10")]
alias Function.Injective.linearOrderedCommMonoid := Function.Injective.isOrderedMonoid
@[deprecated (since := "2025-04-10")]
alias Function.Injective.linearOrderedAddCommMonoid := Function.Injective.isOrderedAddMonoid
@[deprecated (since := "2025-04-10")]
alias Function.Injective.linearOrderedCancelCommMonoid := Function.Injective.isOrderedCancelMonoid
@[deprecated (since := "2025-04-10")]
alias Function.Injective.linearOrderedCancelAddCommMonoid :=
  Function.Injective.isOrderedCancelAddMonoid
@[deprecated (since := "2025-04-10")]
alias Function.Injective.orderedCommGroup := Function.Injective.isOrderedMonoid
@[deprecated (since := "2025-04-10")]
alias Function.Injective.orderedAddCommGroup := Function.Injective.isOrderedAddMonoid
@[deprecated (since := "2025-04-10")]
alias Function.Injective.linearOrderedCommGroup := Function.Injective.isOrderedMonoid
@[deprecated (since := "2025-04-10")]
alias Function.Injective.linearOrderedAddCommGroup := Function.Injective.isOrderedAddMonoid

-- TODO find a better home for the next two constructions.
/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `OrderIso.mulLeft` when working in an ordered group. -/
@[to_additive (attr := simps!)
      /-- The order embedding sending `b` to `a + b`, for some fixed `a`.
       See also `OrderIso.addLeft` when working in an additive ordered group. -/]
def OrderEmbedding.mulLeft {α : Type*} [Mul α] [LinearOrder α]
    [MulLeftStrictMono α] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => m * n) fun _ _ w => mul_lt_mul_left' w m

/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `OrderIso.mulRight` when working in an ordered group. -/
@[to_additive (attr := simps!)
      /-- The order embedding sending `b` to `b + a`, for some fixed `a`.
       See also `OrderIso.addRight` when working in an additive ordered group. -/]
def OrderEmbedding.mulRight {α : Type*} [Mul α] [LinearOrder α]
    [MulRightStrictMono α] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => n * m) fun _ _ w => mul_lt_mul_right' w m
