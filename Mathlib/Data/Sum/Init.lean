/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Init

/-!

This file defines `Sum.get`, the operation that extracts a term of type `α` from `α ⊕ α`.

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.

-/

@[expose] public section

namespace Sum

universe u₁ u₂ u₃ u₄

variable {α : Type u₁} {β : Type u₂} {γ : Sort u₃} {δ : Type u₄}

theorem elim_apply_of_isLeft {f : α → γ} {g : β → γ} {x} (h : x.isLeft) :
    Sum.elim f g x = f (x.getLeft h) := by grind

theorem elim_apply_of_isRight {f : α → γ} {g : β → γ} {x} (h : x.isRight) :
    Sum.elim f g x = g (x.getRight h) := by grind

theorem elim_apply {f : α → γ} {g : β → γ} {x} : Sum.elim f g x =
    if h : x.isLeft then f (x.getLeft h) else g (x.getRight (by grind)) := by cases x <;> simp

@[expose] protected def get : α ⊕ α → α := Sum.elim id id

section

variable {x y : α ⊕ α} {a : α}

@[simp, grind =] theorem get_inl : Sum.get (inl a) = a := rfl
@[simp, grind =] theorem get_inr : Sum.get (inr a) = a := rfl

theorem get_apply_of_isLeft (h : x.isLeft) :
    x.get = x.getLeft h := by grind

theorem get_apply_of_isRight (h : x.isRight) :
    x.get = x.getRight h := by grind

theorem get_apply : Sum.get x = if h : x.isLeft then x.getLeft h else x.getRight (by grind) := by
    grind

@[simp, grind =] theorem get_map {f : β → α} {g : δ → α} {y : β ⊕ δ} :
    (y.map f g).get = y.elim f g := by cases y <;> rfl

theorem map_comp_diag {f : β → α} {g : δ → α} : Sum.get ∘ Sum.map f g = Sum.elim f g :=
  funext fun _ => get_map

theorem surjective_diag : Function.Surjective (Sum.get (α := α)) := fun a => ⟨Sum.inl a, rfl⟩

@[simp, grind =] theorem get_eq_iff : x.get = y.get ↔ x = y ∨ x = y.swap := by grind

end

end Sum
