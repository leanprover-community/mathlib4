/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Classes.SetNotation
import Std.Data.Option.Basic
import Std.Data.List.Lemmas
import Mathlib.Init.Algebra.Classes

/-!
# Extra definitions on `Option`

This file defines more operations involving `Option α`. Lemmas about them are located in other
files under `Data.Option.`.
Other basic operations on `Option` are defined in the core library.
-/

namespace Option

/-- Two arguments failsafe function. Returns `f a b` if the inputs are `some a` and `some b`, and
"does nothing" otherwise. -/
def lift_or_get (f : α → α → α) : Option α → Option α → Option α
| none, none => none
| some a, none => some a
| none, some b => some b
| some a, some b => some (f a b)

/-- Lifts a relation `α → β → Prop` to a relation `option α → option β → Prop` by just adding
`none ~ none`. -/
inductive rel (r : α → β → Prop) : Option α → Option β → Prop
| /-- If `a ~ b`, then `some a ~ some b` -/
  some {a b} : r a b → rel r (some a) (some b)
| /-- `none ~ none` -/
  none : rel r none none

protected def traverse.{u, v} {F : Type u → Type v} [Applicative F] {α β : Type _} (f : α → F β) :
  Option α → F (Option β)
| none => pure none
| some x => some <$> f x

/-- If you maybe have a monadic computation in a `[monad m]` which produces a term of type `α`, then
there is a naturally associated way to always perform a computation in `m` which maybe produces a
result. -/
def maybe.{u, v} {m : Type u → Type v} [Monad m] {α : Type u} : Option (m α) → m (Option α)
| none => pure none
| some fn => some <$> fn

/-- Map a monadic function `f : α → m β` over an `o : option α`, maybe producing a result. -/
def mmap.{u, v, w} {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β)
    (o : Option α) : m (Option β) :=
  (o.map f).maybe

/-- A monadic analogue of `Option.elim`. -/
def melim {α β : Type _} {m : Type _ → Type _} [Monad m] (x : m (Option α)) (y : m β)
    (z : α → m β) : m β :=
  do (← x).elim y z

/-- A monadic analogue of `Option.getD`. -/
def mgetD {α : Type _} {m : Type _ → Type _} [Monad m] (x : m (Option α)) (y : m α) : m α :=
  melim x y pure

variable {α : Type _} {β : Type _}

-- Porting note: Would need to add the attribute directly in `Init.Prelude`.
-- attribute [inline] Option.isSome Option.isNone

-- Porting note: `Option.elim` already present with different argument order.
/-- An elimination principle for `option`. It is a nondependent version of `option.rec`. -/
@[simp]
protected def elim' (b : β) (f : α → β) : Option α → β
  | some a => f a
  | none => b

theorem is_none_iff_eq_none {o : Option α} : o.isNone = true ↔ o = none :=
  ⟨Option.eq_none_of_isNone, fun e => e.symm ▸ rfl⟩

theorem mem_some_iff {α : Type _} {a b : α} : a ∈ some b ↔ b = a := by simp

/-- `o = none` is decidable even if the wrapped type does not have decidable equality.
This is not an instance because it is not definitionally equal to `option.decidable_eq`.
Try to use `o.isNone` or `o.isSome` instead.
-/
@[inline]
def decidableEqNone {o : Option α} : Decidable (o = none) :=
  decidable_of_decidable_of_iff is_none_iff_eq_none

instance decidableForallMem {p : α → Prop} [DecidablePred p] : ∀ o : Option α, Decidable (∀ a ∈ o, p a)
  | none => isTrue (by simp [false_imp_iff])
  | some a => if h : p a then isTrue fun o e => some_inj.1 e ▸ h else isFalse <| mt (fun H => H _ rfl) h

instance decidableExistsMem {p : α → Prop} [DecidablePred p] : ∀ o : Option α, Decidable (∃ a ∈ o, p a)
  | none => isFalse fun ⟨a, ⟨h, _⟩⟩ => by cases h
  | some a => if h : p a then isTrue <| ⟨_, rfl, h⟩ else isFalse fun ⟨_, ⟨rfl, hn⟩⟩ => h hn

/-- Inhabited `get` function. Returns `a` if the input is `some a`, otherwise returns `default`. -/
@[reducible]
def iget [Inhabited α] : Option α → α
  | some x => x
  | none => default

-- Porting note: Illegal simp attribute, left side is `a`
-- @[simp]
theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl

@[simp]
theorem mem_to_list {a : α} {o : Option α} : a ∈ toList o ↔ a ∈ o := by
  cases o <;> simp [toList, eq_comm]

-- lift f
instance lift_or_get_comm (f : α → α → α) [h : IsCommutative α f] : IsCommutative (Option α) (liftOrGet f) :=
  ⟨fun a b => by cases a <;> cases b <;> simp [lift_or_get, IsCommutative.comm]⟩

instance lift_or_get_assoc (f : α → α → α) [h : IsAssociative α f] : IsAssociative (Option α) (liftOrGet f) :=
  ⟨fun a b c => by cases a <;> cases b <;> cases c <;> simp [lift_or_get, IsAssociative.assoc]⟩

instance lift_or_get_idem (f : α → α → α) [h : IsIdempotent α f] : IsIdempotent (Option α) (liftOrGet f) :=
  ⟨fun a => by cases a <;> simp [lift_or_get, IsIdempotent.idempotent]⟩

instance lift_or_get_is_left_id (f : α → α → α) : IsLeftId (Option α) (liftOrGet f) none :=
  ⟨fun a => by cases a <;> simp [lift_or_get]⟩

instance lift_or_get_is_right_id (f : α → α → α) : IsRightId (Option α) (liftOrGet f) none :=
  ⟨fun a => by cases a <;> simp [lift_or_get]⟩

/-- A monadic analogue of `option.get_or_else`. -/
def mgetOrElse {α : Type _} {m : Type _ → Type _} [Monad m] (x : m (Option α)) (y : m α) : m α :=
  melim x y pure
