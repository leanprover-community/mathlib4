/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
import Mathlib.Algebra.Group.WithOne.Defs
import Mathlib.Data.Option.NAry

/-!
# Adjoining a zero/one to semigroups and mapping
-/

variable {α β γ : Type*}

namespace WithOne

/-- Lift a map `f : α → β` to `WithOne α → WithOne β`. Implemented using `Option.map`.

Note: the definition previously known as `WithOne.map` is now called `WithOne.mapMulHom`. -/
@[to_additive
/-- Lift a map `f : α → β` to `WithZero α → WithZero β`. Implemented using `Option.map`.

Note: the definition previously known as `WithZero.map` is now called `WithZero.mapAddHom`. -/]
def map (f : α → β) : WithOne α → WithOne β := Option.map f

@[to_additive (attr := simp)]
theorem map_bot (f : α → β) : map f 1 = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

/-- The image of a binary function `f : α → β → γ` as a function
`WithOne α → WithOne β → WithOne γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
@[to_additive
/-- The image of a binary function `f : α → β → γ` as a function
`WithZero α → WithZero β → WithZero γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/]
def map₂ : (α → β → γ) → WithOne α → WithOne β → WithOne γ := Option.map₂

@[to_additive]
lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl
@[to_additive (attr := simp)]
lemma map₂_bot_left (f : α → β → γ) (b) : map₂ f 1 b = 1 := rfl
@[to_additive (attr := simp)]
lemma map₂_bot_right (f : α → β → γ) (a) : map₂ f a 1 = 1 := by cases a <;> rfl
@[to_additive (attr := simp)]
lemma map₂_coe_left (f : α → β → γ) (a : α) (b) : map₂ f a b = b.map fun b ↦ f a b := rfl
@[to_additive (attr := simp)]
lemma map₂_coe_right (f : α → β → γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by
  cases a <;> rfl

@[to_additive (attr := simp)]
lemma map₂_eq_bot_iff {f : α → β → γ} {a : WithOne α} {b : WithOne β} :
    map₂ f a b = 1 ↔ a = 1 ∨ b = 1 := Option.map₂_eq_none_iff

end WithOne
