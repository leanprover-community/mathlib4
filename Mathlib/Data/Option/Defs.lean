/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

/-!
# Extra definitions on `Option`

This file defines more operations involving `Option α`. Lemmas about them are located in other
files under `Mathlib.Data.Option`.
Other basic operations on `Option` are defined in the core library.
-/

namespace Option

/-- Traverse an object of `Option α` with a function `f : α → F β` for an applicative `F`. -/
protected def traverse.{u, v}
    {F : Type u → Type v} [Applicative F] {α : Type*} {β : Type u} (f : α → F β) :
    Option α → F (Option β)
  | none => pure none
  | some x => some <$> f x

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


theorem mem_some_iff {α : Type*} {a b : α} : a ∈ some b ↔ b = a := by simp

/-- `o = none` is decidable even if the wrapped type does not have decidable equality.
This is not an instance because it is not definitionally equal to `Option.decidableEq`.
Try to use `o.isNone` or `o.isSome` instead.
-/
@[inline]
def decidableEqNone {o : Option α} : Decidable (o = none) :=
  decidable_of_decidable_of_iff isNone_iff_eq_none

instance decidableForallMem {p : α → Prop} [DecidablePred p] :
    ∀ o : Option α, Decidable (∀ a ∈ o, p a)
  | none => isTrue (by simp [false_imp_iff])
  | some a =>
      if h : p a then isTrue fun _ e ↦ some_inj.1 e ▸ h
      else isFalse <| mt (fun H ↦ H _ rfl) h

instance decidableExistsMem {p : α → Prop} [DecidablePred p] :
    ∀ o : Option α, Decidable (∃ a ∈ o, p a)
  | none => isFalse fun ⟨a, ⟨h, _⟩⟩ ↦ by cases h
  | some a => if h : p a then isTrue <| ⟨_, rfl, h⟩ else isFalse fun ⟨_, ⟨rfl, hn⟩⟩ ↦ h hn

/-- Inhabited `get` function. Returns `a` if the input is `some a`, otherwise returns `default`. -/
abbrev iget [Inhabited α] : Option α → α
  | some x => x
  | none => default

theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl

instance zipWith_isCommutative (f : α → α → α) [Std.Commutative f] :
    Std.Commutative (zipWith f) :=
  ⟨fun a b ↦ by cases a <;> cases b <;> simp [zipWith, Std.Commutative.comm]⟩

instance zipWith_isAssociative (f : α → α → α) [Std.Associative f] :
    Std.Associative (zipWith f) :=
  ⟨fun a b c ↦ by cases a <;> cases b <;> cases c <;> simp [zipWith, Std.Associative.assoc]⟩

instance zipWith_isIdempotent (f : α → α → α) [Std.IdempotentOp f] :
    Std.IdempotentOp (zipWith f) :=
  ⟨fun a ↦ by cases a <;> simp [zipWith, Std.IdempotentOp.idempotent]⟩

instance zipWith_isId (f : α → α → α) : Std.LawfulIdentity (zipWith f) none where
  left_id a := by cases a <;> simp [zipWith]
  right_id a := by cases a <;> simp [zipWith]

@[deprecated zipWith_isCommutative (since := "2025-04-04")] abbrev liftOrGet_isCommutative :=
  @zipWith_isCommutative
@[deprecated zipWith_isAssociative (since := "2025-04-04")] abbrev liftOrGet_isAssociative :=
  @zipWith_isAssociative
@[deprecated zipWith_isIdempotent (since := "2025-04-04")] abbrev liftOrGet_isIdempotent :=
  @zipWith_isIdempotent
@[deprecated zipWith_isId (since := "2025-04-04")] abbrev liftOrGet_isId := @zipWith_isId

/-- Convert `undef` to `none` to make an `LOption` into an `Option`. -/
def _root_.Lean.LOption.toOption {α} : Lean.LOption α → Option α
  | .some a => some a
  | _ => none

end Option
