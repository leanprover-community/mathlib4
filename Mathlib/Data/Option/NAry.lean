/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Batteries.Tactic.Init
import Mathlib.Logic.Function.Defs

/-!
# Binary map of options

This file defines the binary map of `Option`. This is mostly useful to define pointwise operations
on intervals.

## Main declarations

* `Option.map₂`: Binary map of options.

## Notes

This file is very similar to the n-ary section of `Mathlib/Data/Set/Basic.lean`, to
`Mathlib/Data/Finset/NAry.lean` and to `Mathlib/Order/Filter/NAry.lean`. Please keep them in sync.

We do not define `Option.map₃` as its only purpose so far would be to prove properties of
`Option.map₂` and casing already fulfills this task.
-/

universe u

open Function

namespace Option

-- Allow `grind` to case split on `Option` in this file.
attribute [local grind cases] Option

variable {α β γ δ : Type*} {f : α → β → γ} {a : Option α} {b : Option β} {c : Option γ}

/-- The image of a binary function `f : α → β → γ` as a function `Option α → Option β → Option γ`.
Mathematically this should be thought of as the image of the corresponding function `α × β → γ`. -/
def map₂ (f : α → β → γ) (a : Option α) (b : Option β) : Option γ :=
  a.bind fun a => b.map <| f a

/-- `Option.map₂` in terms of monadic operations. Note that this can't be taken as the definition
because of the lack of universe polymorphism. -/
theorem map₂_def {α β γ : Type u} (f : α → β → γ) (a : Option α) (b : Option β) :
    map₂ f a b = f <$> a <*> b := by
  cases a <;> rfl

@[simp, grind =]
theorem map₂_some_some (f : α → β → γ) (a : α) (b : β) : map₂ f (some a) (some b) = f a b := rfl

theorem map₂_coe_coe (f : α → β → γ) (a : α) (b : β) : map₂ f a b = f a b := rfl

@[simp, grind =]
theorem map₂_none_left (f : α → β → γ) (b : Option β) : map₂ f none b = none := rfl

@[simp, grind =]
theorem map₂_none_right (f : α → β → γ) (a : Option α) : map₂ f a none = none := by cases a <;> rfl

@[simp]
theorem map₂_coe_left (f : α → β → γ) (a : α) (b : Option β) : map₂ f a b = b.map fun b => f a b :=
  rfl

@[simp]
theorem map₂_coe_right (f : α → β → γ) (a : Option α) (b : β) :
    map₂ f a b = a.map fun a => f a b := by grind

theorem mem_map₂_iff {c : γ} : c ∈ map₂ f a b ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c := by
  grind

/-- `simp`-normal form of `mem_map₂_iff`. -/
@[simp]
theorem map₂_eq_some_iff {c : γ} :
    map₂ f a b = some c ↔ ∃ a' b', a' ∈ a ∧ b' ∈ b ∧ f a' b' = c := by
  grind

@[simp]
theorem map₂_eq_none_iff : map₂ f a b = none ↔ a = none ∨ b = none := by
  grind

theorem map₂_swap (f : α → β → γ) (a : Option α) (b : Option β) :
    map₂ f a b = map₂ (fun a b => f b a) b a := by grind

theorem map_map₂ (f : α → β → γ) (g : γ → δ) :
    (map₂ f a b).map g = map₂ (fun a b => g (f a b)) a b := by grind

theorem map₂_map_left (f : γ → β → δ) (g : α → γ) :
    map₂ f (a.map g) b = map₂ (fun a b => f (g a) b) a b := by grind

theorem map₂_map_right (f : α → γ → δ) (g : β → γ) :
    map₂ f a (b.map g) = map₂ (fun a b => f a (g b)) a b := by grind

@[simp]
theorem map₂_curry (f : α × β → γ) (a : Option α) (b : Option β) :
    map₂ (curry f) a b = Option.map f (map₂ Prod.mk a b) := by grind

@[simp]
theorem map_uncurry (f : α → β → γ) (x : Option (α × β)) :
    x.map (uncurry f) = map₂ f (x.map Prod.fst) (x.map Prod.snd) := by grind

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `Option.map₂` of those operations.
The proof pattern is `map₂_lemma operation_lemma`. For example, `map₂_comm mul_comm` proves that
`map₂ (*) a b = map₂ (*) g f` in a `CommSemigroup`.
-/

variable {α' β' δ' ε ε' : Type*}

theorem map₂_assoc {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
    (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    map₂ f (map₂ g a b) c = map₂ f' a (map₂ g' b c) := by grind

theorem map₂_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : map₂ f a b = map₂ g b a := by
  grind

theorem map₂_left_comm {f : α → δ → ε} {g : β → γ → δ} {f' : α → γ → δ'} {g' : β → δ' → ε}
    (h_left_comm : ∀ a b c, f a (g b c) = g' b (f' a c)) :
    map₂ f a (map₂ g b c) = map₂ g' b (map₂ f' a c) := by grind

theorem map₂_right_comm {f : δ → γ → ε} {g : α → β → δ} {f' : α → γ → δ'} {g' : δ' → β → ε}
    (h_right_comm : ∀ a b c, f (g a b) c = g' (f' a c) b) :
    map₂ f (map₂ g a b) c = map₂ g' (map₂ f' a c) b := by grind

theorem map_map₂_distrib {g : γ → δ} {f' : α' → β' → δ} {g₁ : α → α'} {g₂ : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' (g₁ a) (g₂ b)) :
    (map₂ f a b).map g = map₂ f' (a.map g₁) (b.map g₂) := by grind

/-!
The following symmetric restatement are needed because unification has a hard time figuring all the
functions if you symmetrize on the spot. This is also how the other n-ary APIs do it.
-/

/-- Symmetric statement to `Option.map₂_map_left_comm`. -/
theorem map_map₂_distrib_left {g : γ → δ} {f' : α' → β → δ} {g' : α → α'}
    (h_distrib : ∀ a b, g (f a b) = f' (g' a) b) :
    (map₂ f a b).map g = map₂ f' (a.map g') b := by grind

/-- Symmetric statement to `Option.map_map₂_right_comm`. -/
theorem map_map₂_distrib_right {g : γ → δ} {f' : α → β' → δ} {g' : β → β'}
    (h_distrib : ∀ a b, g (f a b) = f' a (g' b)) : (map₂ f a b).map g = map₂ f' a (b.map g') := by
  grind

/-- Symmetric statement to `Option.map_map₂_distrib_left`. -/
theorem map₂_map_left_comm {f : α' → β → γ} {g : α → α'} {f' : α → β → δ} {g' : δ → γ}
    (h_left_comm : ∀ a b, f (g a) b = g' (f' a b)) : map₂ f (a.map g) b = (map₂ f' a b).map g' := by
  grind

/-- Symmetric statement to `Option.map_map₂_distrib_right`. -/
theorem map_map₂_right_comm {f : α → β' → γ} {g : β → β'} {f' : α → β → δ} {g' : δ → γ}
    (h_right_comm : ∀ a b, f a (g b) = g' (f' a b)) :
    map₂ f a (b.map g) = (map₂ f' a b).map g' := by grind

theorem map_map₂_antidistrib {g : γ → δ} {f' : β' → α' → δ} {g₁ : β → β'} {g₂ : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (map₂ f a b).map g = map₂ f' (b.map g₁) (a.map g₂) := by grind

/-- Symmetric statement to `Option.map₂_map_left_anticomm`. -/
theorem map_map₂_antidistrib_left {g : γ → δ} {f' : β' → α → δ} {g' : β → β'}
    (h_antidistrib : ∀ a b, g (f a b) = f' (g' b) a) :
    (map₂ f a b).map g = map₂ f' (b.map g') a := by grind

/-- Symmetric statement to `Option.map_map₂_right_anticomm`. -/
theorem map_map₂_antidistrib_right {g : γ → δ} {f' : β → α' → δ} {g' : α → α'}
    (h_antidistrib : ∀ a b, g (f a b) = f' b (g' a)) :
    (map₂ f a b).map g = map₂ f' b (a.map g') := by grind

/-- Symmetric statement to `Option.map_map₂_antidistrib_left`. -/
theorem map₂_map_left_anticomm {f : α' → β → γ} {g : α → α'} {f' : β → α → δ} {g' : δ → γ}
    (h_left_anticomm : ∀ a b, f (g a) b = g' (f' b a)) :
    map₂ f (a.map g) b = (map₂ f' b a).map g' := by grind

/-- Symmetric statement to `Option.map_map₂_antidistrib_right`. -/
theorem map_map₂_right_anticomm {f : α → β' → γ} {g : β → β'} {f' : β → α → δ} {g' : δ → γ}
    (h_right_anticomm : ∀ a b, f a (g b) = g' (f' b a)) :
    map₂ f a (b.map g) = (map₂ f' b a).map g' := by grind

/-- If `a` is a left identity for a binary operation `f`, then `some a` is a left identity for
`Option.map₂ f`. -/
lemma map₂_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (o : Option β) :
    map₂ f (some a) o = o := by grind

/-- If `b` is a right identity for a binary operation `f`, then `some b` is a right identity for
`Option.map₂ f`. -/
lemma map₂_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (o : Option α) :
    map₂ f o (some b) = o := by grind

end Option
