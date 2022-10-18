/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Classes.SetNotation
import Std.Data.Option.Basic

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
