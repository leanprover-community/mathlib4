/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Batteries.Tactic.Alias

/-!
# Extra definitions on `Option`

This file defines more operations involving `Option α`. Lemmas about them are located in other
files under `Mathlib/Data/Option.lean`.
Other basic operations on `Option` are defined in the core library.
-/

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
abbrev iget [Inhabited α] : Option α → α
  | some x => x
  | none => default

theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl

@[deprecated commutative_merge (since := "2025-06-03")]
theorem merge_isCommutative (f : α → α → α) [Std.Commutative f] :
    Std.Commutative (merge f) := commutative_merge f

@[deprecated associative_merge (since := "2025-06-03")]
theorem merge_isAssociative (f : α → α → α) [Std.Associative f] :
    Std.Associative (merge f) := associative_merge f

@[deprecated idempotentOp_merge (since := "2025-06-03")]
theorem merge_isIdempotent (f : α → α → α) [Std.IdempotentOp f] :
    Std.IdempotentOp (merge f) := idempotentOp_merge f

@[deprecated lawfulIdentity_merge (since := "2025-06-03")]
theorem merge_isId (f : α → α → α) : Std.LawfulIdentity (merge f) none := lawfulIdentity_merge f

@[deprecated (since := "2025-04-04")] alias liftOrGet_isCommutative :=
  merge_isCommutative
@[deprecated (since := "2025-04-04")] alias liftOrGet_isAssociative :=
  merge_isAssociative
@[deprecated (since := "2025-04-04")] alias liftOrGet_isIdempotent :=
  merge_isIdempotent
@[deprecated (since := "2025-04-04")] alias liftOrGet_isId := merge_isId

end Option
