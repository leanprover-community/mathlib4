/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init.Algebra.Classes
import Mathlib.Init.Logic
import Mathlib.Mathport.Rename

/-!
# Extra definitions on `Option`

This file defines more operations involving `Option α`. Lemmas about them are located in other
files under `Data.Option.`.
Other basic operations on `Option` are defined in the core library.
-/

namespace Option

variable {α : Type _} {β : Type _}

/-- An elimination principle for `Option`. It is a nondependent version of `Option.Rec`. -/
@[simp]
protected def elimₓ (b : β) (f : α → β) : Option α → β
  | some a => f a
  | none => b

instance hasMem : Membership α (Option α) :=
  ⟨fun a b => b = some a⟩

theorem mem_some_iff {α : Type _} {a b : α} : a ∈ some b ↔ b = a := by simp

/-- `o = none` is decidable even if the wrapped type does not have decidable equality.

This is not an instance because it is not definitionally equal to `Option.DecidableEq`.
Try to use `o.isNone` or `o.isSome` instead.
-/
@[inline]
def decidableEqNone {o : Option α} : Decidable (o = none) :=
  decidable_of_decidable_of_iff isNone_iff_eq_none

instance decidableForallMem {p : α → Prop} [DecidablePred p] :
    ∀ o : Option α, Decidable (∀ (a : α) (_ : a ∈ o), p a)
  | none => isTrue (by simp [false_imp_iff])
  | some a => if h : p a then isTrue fun o e => some_inj.1 e ▸ h
      else isFalse <| mt (fun H => H _ rfl) h

instance decidableExistsMem {p : α → Prop} [DecidablePred p] :
    ∀ o : Option α, Decidable (∃ a ∈ o, p a)
  | none => isFalse fun ⟨a, ⟨h, _⟩⟩ => by cases h
  | some a => if h : p a then isTrue <| ⟨_, rfl, h⟩ else isFalse fun ⟨_, ⟨rfl, hn⟩⟩ => h hn

/-- Inhabited `get` function. Returns `a` if the input is `some a`, otherwise returns `default`. -/
@[reducible]
def iget [Inhabited α] : Option α → α
  | some x => x
  | none => default

-- invalid `simp` theorem, equation is equivalent to
--  a = a
-- @[simp]
theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl

@[simp]
theorem mem_toList {a : α} {o : Option α} : a ∈ toList o ↔ a ∈ o := by
  cases o <;> simp [toList, eq_comm]

#align option.mem_to_list Option.mem_toList

instance (f : α → α → α) [h : IsCommutative α f] :
    IsCommutative (Option α) (liftOrGet f) :=
  ⟨fun a b => by cases a <;> cases b <;> simp only [liftOrGet, some_inj] <;> rw [h.comm]⟩

instance (f : α → α → α) [h : IsAssociative α f] :
    IsAssociative (Option α) (liftOrGet f) :=
  ⟨fun a b c => by cases a <;> cases b <;> cases c <;> simp only [liftOrGet, some_inj] <;>
    rw [h.assoc]⟩

instance (f : α → α → α) [h : IsIdempotent α f] : IsIdempotent (Option α) (liftOrGet f) :=
  ⟨fun a => by cases a <;> simp only [liftOrGet, some_inj] <;> rw [h.idempotent]⟩

instance (f : α → α → α) : IsLeftId (Option α) (liftOrGet f) none :=
  ⟨fun a => by cases a <;> simp [liftOrGet]⟩

instance (f : α → α → α) : IsRightId (Option α) (liftOrGet f) none :=
  ⟨fun a => by cases a <;> simp [liftOrGet]⟩

protected def traverse.{u, v} {F : Type u → Type v} [Applicative F] {α β : Type _} (f : α → F β) :
    Option α → F (Option β)
  | none => pure none
  | some x => some <$> f x

/-- If you maybe have a monadic computation in a `[Monad m]` which produces a term of type `α`, then
there is a naturally associated way to always perform a computation in `m` which maybe produces a
result. -/
def maybe.{u, v} {m : Type u → Type v} [Monad m] {α : Type u} : Option (m α) → m (Option α)
  | none => return none
  | some fn => some <$> fn

/-- Map a monadic function `f : α → m β` over an `o : Option α`, maybe producing a result. -/
def mmap.{u, v, w} {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β)
    (o : Option α) : m (Option β) :=
  (o.map f).maybe

/-- A monadic analogue of `Option.elim`. -/
def melim {α β : Type _} {m : Type _ → Type _} [Monad m] (y : m β) (z : α → m β)
    (x : m (Option α)) : m β :=
  x >>= Option.elimₓ y z

/-- A monadic analogue of `Option.getOrElse`. -/
def mgetOrElse {α : Type _} {m : Type _ → Type _} [Monad m] (x : m (Option α)) (y : m α) : m α :=
  melim y pure x

end Option
