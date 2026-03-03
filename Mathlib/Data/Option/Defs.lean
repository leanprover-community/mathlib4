/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Tactic.Lemma
public import Mathlib.Tactic.TypeStar

/-!
# Extra definitions on `Option`

This file defines more operations involving `Option α`. Lemmas about them are located in other
files under `Mathlib/Data/Option/`.
Other basic operations on `Option` are defined in the core library.
-/

@[expose] public section

namespace Option

/-- Traverse an object of `Option α` with a function `f : α → F β` for an applicative `F`. -/
protected def traverse.{u, v}
    {F : Type u → Type v} [Applicative F] {α : Type*} {β : Type u} (f : α → F β) :
    Option α → F (Option β) := Option.mapA f

variable {α : Type*} {β : Type*}

/-- An elimination principle for `Option`. It is a nondependent version of `Option.rec`. -/
protected def elim' (b : β) (f : α → β) : Option α → β
  | some a => f a
  | none => b

@[simp]
theorem elim'_none (b : β) (f : α → β) : Option.elim' b f none = b := rfl

@[simp]
theorem elim'_some {a : α} (b : β) (f : α → β) : Option.elim' b f (some a) = f a := rfl

@[simp]
theorem elim'_none_some (f : Option α → β) : (Option.elim' (f none) (f ∘ some)) = f :=
  funext fun o ↦ by cases o <;> rfl

lemma elim'_eq_elim {α β : Type*} (b : β) (f : α → β) (a : Option α) :
    Option.elim' b f a = Option.elim a b f := by
  cases a <;> rfl

/-- Inhabited `get` function. Returns `a` if the input is `some a`, otherwise returns `default`. -/
@[deprecated "Use `Option.get!` (which will panic on `none`) or \
    `Option.getD` (which takes an explicit default value)." (since := "2026-01-05")]
abbrev iget [Inhabited α] : Option α → α
  | some x => x
  | none => default

set_option linter.deprecated false in
@[deprecated "Use `Option.getD`." (since := "2026-01-05")]
theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl

end Option
