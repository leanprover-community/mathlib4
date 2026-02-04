/-
Copyright (c) 2017 Anthony Vandikas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas
-/
module

import Mathlib.Data.Option.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Order.Monotone.Defs

/-!
# Orders on an Option type

This file provides various order-related lemmas and instances for the `Option` type.
-/

public section

variable {α : Type*}

namespace Option

instance [Preorder α] : Preorder (Option α) where
  le_refl a := by cases a <;> grind
  le_trans a b c h₁ h₂ := by cases a <;> cases b <;> cases c <;> grind
  lt_iff_le_not_ge a b := by cases a <;> cases b <;> grind [lt_iff_le_not_ge]

instance [PartialOrder α] : PartialOrder (Option α) where
  le_antisymm a b := by cases a <;> cases b <;> grind

instance : Bot (Option α) where
  bot := none

instance [LE α] : OrderBot (Option α) where
  bot_le _ := none_le

lemma some_mono [Preorder α] : Monotone (some : α → Option α) := by
  simp only [Monotone, some_le_some, imp_self, implies_true]

lemma get_mono [Preorder α] {x : Option α} {y : Option α}
    (hx : x.isSome) (hy : y.isSome) (h : x ≤ y) :
    x.get hx ≤ y.get hy := by
  cases x
  · simp at hx
  · cases y <;> simp_all

lemma isSome_mono [Preorder α] : Monotone (isSome : Option α → Bool)
  | none, _, _ => by simp only [isSome_none, Bool.false_le]
  | _, none, _ => by simp_all only [le_none, isSome_none, le_refl]
  | some x, some y, h => by simp only [isSome_some, le_refl]

lemma bind_mono {β γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
    {f : α → Option β} (hf : Monotone f)
    {g : α → β → Option γ} (hg : Monotone (Function.uncurry g)) :
    Monotone (fun x ↦ Option.bind (f x) (g x)) := by
  intro x₁ x₂ hx
  cases hfx₁ : f x₁
  · grind
  · cases hfx₂ : f x₂
    · grind [Monotone]
    · simp only [hfx₁, bind_some, hfx₂]
      apply hg (Prod.GCongr.mk_le_mk hx ?_)
      grind [Monotone]

lemma map_mono
    [Preorder α]
    {β : Type*} [Preorder β]
    {γ : Type*} [Preorder γ]
    {f : α → β → γ} (hf : Monotone fun x : _ × _ ↦ f x.1 x.2)
    {g : α → Option β} (hg : Monotone g)
    : Monotone (fun x ↦ Option.map (f x) (g x)) := by
  simp only [map_eq_bind, Function.comp_apply]
  exact bind_mono hg (Monotone.comp some_mono hf)

end Option
