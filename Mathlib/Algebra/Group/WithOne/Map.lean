/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.Data.Option.NAry

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Adjoining a zero/one to semigroups and mapping
-/

@[expose] public section

variable {α β γ : Type*}

namespace WithOne

/-- Lift a map `f : α → β` to `WithOne α → WithOne β`. Implemented using `Option.map`.

Note: the definition previously known as `WithOne.map` is now called `WithOne.mapMulHom`. -/
@[to_additive
/-- Lift a map `f : α → β` to `WithZero α → WithZero β`. Implemented using `Option.map`.

Note: the definition previously known as `WithZero.map` is now called `WithZero.mapAddHom`. -/]
def map (f : α → β) : WithOne α → WithOne β
  | 1 => 1
  | some x => some (f x)

@[to_additive (attr := simp)]
protected theorem map_one (f : α → β) : map f 1 = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem map_coe (f : α → β) (a : α) : map f a = f a :=
  rfl

@[to_additive (attr := simp)]
theorem map_id : map (id : α → α) = id :=
  funext (fun o => match o with | one => rfl | some _ => rfl)

@[to_additive (attr := simp)]
theorem map_map (h : β → γ) (g : α → β) (a : WithOne α) : map h (map g a) = map (h ∘ g) a := by
  cases a <;> simp

/-- The image of a binary function `f : α → β → γ` as a function
`WithOne α → WithOne β → WithOne γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
@[to_additive
/-- The image of a binary function `f : α → β → γ` as a function
`WithZero α → WithZero β → WithZero γ`.

Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/]
def map₂ (f : α → β → γ) : WithOne α → WithOne β → WithOne γ
  | 1, _ => 1
  | _, 1 => 1
  | some x, some y => some (f x y)


@[to_additive (attr := simp)]
lemma map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl
@[to_additive (attr := simp)]
lemma map₂_one_left (f : α → β → γ) (b) : map₂ f 1 b = 1 := rfl
@[to_additive (attr := simp)]
lemma map₂_one_right (f : α → β → γ) (a) : map₂ f a 1 = 1 := by cases a <;> rfl
@[to_additive (attr := simp)]
lemma map₂_coe_left (f : α → β → γ) (a : α) (b) : map₂ f a b = b.map fun b ↦ f a b := by
  cases b <;> simp
@[to_additive (attr := simp)]
lemma map₂_coe_right (f : α → β → γ) (a) (b : β) : map₂ f a b = a.map (f · b) := by
  cases a <;> rfl

@[to_additive]
lemma map₂_eq_comp_comp {f : α → β → γ} (a : WithOne α) (b : WithOne β) :
    map₂ f a b = (toOption γ).symm (Option.map₂ f (toOption α a) (toOption β b)) := by
  cases a <;> cases b <;> rfl

@[to_additive]
lemma map₂_assoc {δ ε ε' : Type*} {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε}
    {g' : β → γ → ε'} (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c))
    {x : WithOne α} {y : WithOne β} {z : WithOne γ} :
    map₂ f (map₂ g x y) z = map₂ f' x (map₂ g' y z) := by
  rw [map₂_eq_comp_comp x y, map₂_eq_comp_comp _ z, map₂_eq_comp_comp y z, map₂_eq_comp_comp x]
  simp [Option.map₂_assoc h_assoc]

@[to_additive]
lemma map₂_comm {f : α → β → γ} {g : β → α → γ} {x : WithOne α} {y : WithOne β}
    (h_comm : ∀ a b, f a b = g b a) : map₂ f x y = map₂ g y x := by
  rw [map₂_eq_comp_comp x y, map₂_eq_comp_comp y x]
  simp [Option.map₂_comm h_comm]

@[to_additive]
lemma map₂_left_identity {a : α} {f : α → β → β} (h : ∀ b, f a b = b) (y : WithOne β) :
    map₂ f a y = y := by cases y <;> simp [h]

@[to_additive]
lemma map₂_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (x : WithOne α) :
    map₂ f x b = x := by cases x <;> simp [h]

@[to_additive (attr := simp)]
lemma map₂_eq_one_iff {f : α → β → γ} {a : WithOne α} {b : WithOne β} :
    map₂ f a b = 1 ↔ a = 1 ∨ b = 1 where
  mp h := by
    contrapose! h
    cases a <;> cases b
    rotate_right
    · simp
    all_goals grind
  mpr h := by cases h <;> simp_all

end WithOne
