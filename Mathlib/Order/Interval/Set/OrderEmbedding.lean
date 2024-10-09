/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Order.Hom.Basic

/-!
# Preimages of intervals under order embeddings

In this file we prove that the preimage of an interval in the codomain under an `OrderEmbedding`
is an interval in the domain.

Note that similar statements about images require the range to be order-connected.
-/

open Set

namespace OrderEmbedding

variable {α β : Type*}

section Preorder

variable [Preorder α] [Preorder β] (e : α ↪o β) (x y : α)

@[simp] theorem preimage_Ici : e ⁻¹' Ici (e x) = Ici x := ext fun _ ↦ e.le_iff_le
@[simp] theorem preimage_Iic : e ⁻¹' Iic (e x) = Iic x := ext fun _ ↦ e.le_iff_le
@[simp] theorem preimage_Ioi : e ⁻¹' Ioi (e x) = Ioi x := ext fun _ ↦ e.lt_iff_lt
@[simp] theorem preimage_Iio : e ⁻¹' Iio (e x) = Iio x := ext fun _ ↦ e.lt_iff_lt

@[simp] theorem preimage_Icc : e ⁻¹' Icc (e x) (e y) = Icc x y := by ext; simp
@[simp] theorem preimage_Ico : e ⁻¹' Ico (e x) (e y) = Ico x y := by ext; simp
@[simp] theorem preimage_Ioc : e ⁻¹' Ioc (e x) (e y) = Ioc x y := by ext; simp
@[simp] theorem preimage_Ioo : e ⁻¹' Ioo (e x) (e y) = Ioo x y := by ext; simp

end Preorder

variable [LinearOrder α]

@[simp] theorem preimage_uIcc [Lattice β] (e : α ↪o β) (x y : α) :
    e ⁻¹' (uIcc (e x) (e y)) = uIcc x y := by
  cases le_total x y <;> simp [*]

@[simp] theorem preimage_uIoc [LinearOrder β] (e : α ↪o β) (x y : α) :
    e ⁻¹' (uIoc (e x) (e y)) = uIoc x y := by
  cases le_total x y <;> simp [*]

end OrderEmbedding
