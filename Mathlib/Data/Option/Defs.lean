/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init.SetNotation

/-!
# Extra definitions on `Option`

This file defines more operations involving `Option α`. Lemmas about them are located in other
files under `Data.Option.`.
Other basic operations on `Option` are defined in the core library.
-/


namespace Option

variable {α : Type _} {β : Type _}

/-- An elimination principle for `Option`. It is a nondependent version of `Option.rec_on`. -/
@[simp]
protected def elim : Option α → β → (α → β) → β
| some x, y, f => f x
| none, y, f => y

instance : Membership α (Option α) :=
  ⟨fun a b => b = some a⟩

@[simp]
theorem mem_def {a : α} {b : Option α} : a ∈ b ↔ b = some a :=
  Iff.rfl

theorem mem_iff {a : α} {b : Option α} : a ∈ b ↔ b = a :=
  Iff.rfl

theorem isNone_iff_eq_none {o : Option α} : o.isNone ↔ o = none :=
  ⟨Option.eq_none_of_isNone, fun e => e.symm ▸ rfl⟩

theorem some_inj {a b : α} : some a = some b ↔ a = b := by simp

/--
`o = none` is decidable even if the wrapped type does not have decidable equality.
This is not an instance because it is not definitionally equal to `Option.decidable_eq`.
Try to use `o.is_none` or `o.is_some` instead.
-/
@[inline]
def decidable_eq_none {o : Option α} : Decidable (o = none) :=
  decidable_of_decidable_of_iff isNone_iff_eq_none

instance decidable_forall_mem {p : α → Prop} [DecidablePred p] :
  ∀ o : Option α, Decidable (∀ a ∈ o, p a)
| none => isTrue (by simp)
| some a =>
  if h : p a then isTrue fun o e => some_inj.1 e ▸ h
  else isFalse $ mt (fun H => H _ rfl) h

instance decidable_exists_mem {p : α → Prop} [DecidablePred p] : ∀ o : Option α, Decidable (∃ a ∈ o, p a)
| none => isFalse fun ⟨a, ⟨h, _⟩⟩ => by cases h
| some a => if h : p a then isTrue ⟨_, rfl, h⟩ else isFalse fun ⟨_, ⟨rfl, hn⟩⟩ => h hn

/-- `guard p a` returns `some a` if `p a` holds, otherwise `none`. -/
def guard (p : α → Prop) [DecidablePred p] (a : α) : Option α :=
  if p a then some a else none

/-- Cast of `Option` to `List`. Returns `[a]` if the input is `some a`, and `[]` if it is
`none`. -/
def toList : Option α → List α
| none => []
| some a => [a]

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

/-- Partial bind. If for some `x : option α`, `f : Π (a : α), a ∈ x → option β` is a
  partial function defined on `a : α` giving an `option β`, where `some a = x`,
  then `pbind x f h` is essentially the same as `bind x f`
  but is defined only when all `x = some a`, using the proof to apply `f`. -/
@[simp]
def pbind : ∀ x : Option α, (∀ a : α, a ∈ x → Option β) → Option β
| none, _ => none
| some a, f => f a rfl

-- ././Mathport/Syntax/Translate/Basic.lean:452:2: warning: expanding binder collection (a «expr ∈ » x)
/-- Partial map. If `f : Π a, p a → β` is a partial function defined on `a : α` satisfying `p`,
then `pmap f x h` is essentially the same as `map f x` but is defined only when all members of `x`
satisfy `p`, using the proof to apply `f`. -/
@[simp]
def pmap {p : α → Prop} (f : ∀ a : α, p a → β) : ∀ x : Option α, (∀ a ∈ x, p a) → Option β
| none, _ => none
| some a, H => some (f a (H a (mem_def.mpr rfl)))

/-- Flatten an `option` of `option`, a specialization of `mjoin`. -/
@[simp]
def join : Option (Option α) → Option α :=
  fun x => x.bind id

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
def mmap.{u, v, w} {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u} (f : α → m β) (o : Option α) :
  m (Option β) :=
  (o.map f).maybe

/-- A monadic analogue of `Option.elim`. -/
def melim {α β : Type _} {m : Type _ → Type _} [Monad m] (x : m (Option α)) (y : m β) (z : α → m β) : m β :=
  do (← x).elim y z

/-- A monadic analogue of `Option.getD`. -/
def mgetD {α : Type _} {m : Type _ → Type _} [Monad m] (x : m (Option α)) (y : m α) : m α :=
  melim x y pure

end Option
