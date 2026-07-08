/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Order.Hom.Basic

/-!
# Ordered monoids

This file develops some additional material on ordered monoids.
-/

@[expose] public section


open Function

universe u

variable {α : Type u} {β : Type*} [CommMonoid α] [Preorder α]

/-- Pullback an `IsOrderedMonoid` under an injective map. -/
@[to_additive /-- Pullback an `IsOrderedAddMonoid` under an injective map. -/]
lemma Function.Injective.isOrderedMonoid [IsOrderedMonoid α] [CommMonoid β]
    [Preorder β] (f : β → α) (mul : ∀ x y, f (x * y) = f x * f y)
    (le : ∀ {x y}, f x ≤ f y ↔ x ≤ y) :
    IsOrderedMonoid β where
  mul_le_mul_left a b ab c := le.1 <| by rw [mul, mul]; grw [le.2 ab]

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
    [Preorder β]
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

-- TODO find a better home for the next two constructions.
/-- The order embedding sending `b` to `a * b`, for some fixed `a`.
See also `OrderIso.mulLeft` when working in an ordered group. -/
@[to_additive (attr := simps!)
      /-- The order embedding sending `b` to `a + b`, for some fixed `a`.
       See also `OrderIso.addLeft` when working in an additive ordered group. -/]
def OrderEmbedding.mulLeft {α : Type*} [Mul α] [LinearOrder α]
    [MulLeftStrictMono α] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => m * n) mul_right_strictMono

/-- The order embedding sending `b` to `b * a`, for some fixed `a`.
See also `OrderIso.mulRight` when working in an ordered group. -/
@[to_additive (attr := simps!)
      /-- The order embedding sending `b` to `b + a`, for some fixed `a`.
       See also `OrderIso.addRight` when working in an additive ordered group. -/]
def OrderEmbedding.mulRight {α : Type*} [Mul α] [LinearOrder α]
    [MulRightStrictMono α] (m : α) : α ↪o α :=
  OrderEmbedding.ofStrictMono (fun n => n * m) mul_left_strictMono


-- Dual/order lemmas discovered by the Manifold Destiny verifier-mediated learner.
-- Paper: https://github.com/sumofagents/manifold-destiny
section
theorem Cardinal.aleph_min : ∀ (o₁ o₂ : Ordinal.{u_1}), Cardinal.aleph (min o₁ o₂) = min (Cardinal.aleph o₁) (Cardinal.aleph o₂) := by
  open Cardinal Function Set Equiv Order Ordinal in
    intro o₁ o₂
    exact (aleph.monotone.map_min)

theorem Ordinal.omega_min : ∀ (o₁ o₂ : Ordinal.{u_1}), Ordinal.omega (min o₁ o₂) = min (Ordinal.omega o₁) (Ordinal.omega o₂) := by
  open Ordinal Function Set Cardinal Equiv Order in
    intro o₁ o₂
    exact (omega.monotone.map_min)

theorem Cardinal.preAleph_min : ∀ (o₁ o₂ : Ordinal.{u_1}), Cardinal.preAleph (min o₁ o₂) = min (Cardinal.preAleph o₁) (Cardinal.preAleph o₂) := by
  open Cardinal Function Set Equiv Order Ordinal in
    intro o₁ o₂
    exact (preAleph.monotone.map_min)

theorem Ordinal.preOmega_min : ∀ (o₁ o₂ : Ordinal.{u_1}), Ordinal.preOmega (min o₁ o₂) = min (Ordinal.preOmega o₁) (Ordinal.preOmega o₂) := by
  open Ordinal Function Set Cardinal Equiv Order in
    intro o₁ o₂
    exact (preOmega.monotone.map_min)

end
