/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Order.WithBot.Basic

set_option autoImplicit true

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of
`WithBot.map₂` / `WithTop.map₂` of those operations.
The proof pattern is `map₂_lemma operation_lemma`. For example, `map₂_comm mul_comm` proves that
`map₂ (*) a b = map₂ (*) g f` in a `CommSemigroup`.

This is a subset of the lemmas from `Mathlib.Data.Option.NAry`.
-/

namespace WithBot

variable {α β δ ε γ ε' : Type*}

attribute [local grind cases] WithBot

theorem map₂_assoc {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
    (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    map₂ f (map₂ g a b) c = map₂ f' a (map₂ g' b c) := by
  grind

theorem map₂_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : map₂ f a b = map₂ g b a := by
  grind

/-- If `a` is a left identity for a binary operation `f`, then `some a` is a left identity for
`WithBot.map₂ f`. -/
lemma map₂_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (o : WithBot β) :
    map₂ f (some a) o = o := by grind

/-- If `b` is a right identity for a binary operation `f`, then `some b` is a right identity for
`WithBot.map₂ f`. -/
lemma map₂_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (o : WithBot α) :
    map₂ f o (some b) = o := by grind

end WithBot

namespace WithTop

variable {α β δ ε γ ε' : Type*}

theorem map₂_assoc {f : δ → γ → ε} {g : α → β → δ} {f' : α → ε' → ε} {g' : β → γ → ε'}
    (h_assoc : ∀ a b c, f (g a b) c = f' a (g' b c)) :
    map₂ f (map₂ g a b) c = map₂ f' a (map₂ g' b c) :=
  WithBot.map₂_assoc h_assoc

theorem map₂_comm {g : β → α → γ} (h_comm : ∀ a b, f a b = g b a) : map₂ f a b = map₂ g b a :=
  WithBot.map₂_comm h_comm

/-- If `a` is a left identity for a binary operation `f`, then `some a` is a left identity for
`WithTop.map₂ f`. -/
lemma map₂_left_identity {f : α → β → β} {a : α} (h : ∀ b, f a b = b) (o : WithTop β) :
    map₂ f (some a) o = o :=
  WithBot.map₂_left_identity h o

/-- If `b` is a right identity for a binary operation `f`, then `some b` is a right identity for
`WithTop.map₂ f`. -/
lemma map₂_right_identity {f : α → β → α} {b : β} (h : ∀ a, f a b = a) (o : WithTop α) :
    map₂ f o (some b) = o :=
  WithBot.map₂_right_identity h o

end WithTop
