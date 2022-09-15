/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init.Data.Option.Instances
import Mathlib.Init.Function
import Mathlib.Data.Option.Defs
import Mathlib.Logic.Basic

namespace Option

theorem some_injective (α : Type _) : Function.injective (@some α) :=
  fun _ _ => some_inj.mp

/-- `option.map f` is injective if `f` is injective. -/
theorem map_injective {f : α → β} (Hf : Function.injective f) : Function.injective (Option.map f)
| none, none, _ => rfl
| some a₁, some a₂, H => by rw [Hf (Option.some.inj H)]

-- theorem join_eq_none {o : Option (Option α)} : o.join = none ↔ o = none ∨ o = some none := by
--   rcases o with _|_|_; simp

theorem lift_or_get_choice {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
  ∀ o₁ o₂, lift_or_get f o₁ o₂ = o₁ ∨ lift_or_get f o₁ o₂ = o₂
| none, none => Or.inl rfl
| some a, none => Or.inl rfl
| none, some b => Or.inr rfl
| some a, some b => by have := h a b; simp [lift_or_get] at this ⊢; exact this

@[simp] theorem lift_or_get_none_left {f} {b : Option α} : lift_or_get f none b = b := by
  cases b <;> rfl

@[simp] theorem lift_or_get_none_right {f} {a : Option α} : lift_or_get f a none = a := by
  cases a <;> rfl

@[simp] theorem lift_or_get_some_some {f} {a b : α} :
  lift_or_get f (some a) (some b) = f a b := rfl
