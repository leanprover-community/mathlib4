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

lemma get_mono
    [Preorder α]
    {x : Option α} (hx : x.isSome)
    {y : Option α} (hy : y.isSome)
    (h : x ≤ y)
    : x.get hx ≤ y.get hy := by
  cases x
  · simp only [isSome_none, Bool.false_eq_true] at hx
  cases y
  · simp only [isSome_none, Bool.false_eq_true] at hy
  simp_all only [some_le_some, get_some]

lemma isSome_mono [Preorder α] : Monotone (isSome : Option α → Bool)
  | none, _, _ => by simp only [isSome_none, Bool.false_le]
  | _, none, _ => by simp_all only [le_none, isSome_none, le_refl]
  | some x, some y, h => by simp only [isSome_some, le_refl]

lemma bind_mono
    [Preorder α]
    {β : Type*} [Preorder β]
    {γ : Type*} [Preorder γ]
    {f : α → Option β} (hf : Monotone f)
    {g : α → β → Option γ} (hg : Monotone fun x : _ × _ ↦ g x.1 x.2)
    : Monotone (fun x ↦ Option.bind (f x) (g x)) := by
  intro x₁ x₂ hx
  dsimp only
  cases hfx₁ : f x₁ with
  | none => simp only [bind_none, none_le]
  | some x =>
    specialize hf hx
    cases hfx₂ : f x₂ with
    | none => grind
    | some y =>
      simp only [hfx₁, hfx₂, some_le_some] at hf
      simp only [bind_some]
      apply hg (?_ : (_, _) ≤ (_, _))
      simp only [ge_iff_le, Prod.mk_le_mk, hx, true_and, hf]

lemma map_mono
    [Preorder α]
    {β : Type*} [Preorder β]
    {γ : Type*} [Preorder γ]
    {f : α → β → γ} (hf : Monotone fun x : _ × _ ↦ f x.1 x.2)
    {g : α → Option β} (hg : Monotone g)
    : Monotone (fun x ↦ Option.map (f x) (g x)) := by
  simp only [map_eq_bind, Function.comp_apply]
  apply bind_mono hg (Monotone.comp some_mono hf)

end Option
