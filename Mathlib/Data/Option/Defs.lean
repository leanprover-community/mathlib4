/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.option.defs
! leanprover-community/mathlib commit c4658a649d216f57e99621708b09dcb3dcccbd23
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Init.Algebra.Classes

/-!
# Extra definitions on `Option`

This file defines more operations involving `Option α`. Lemmas about them are located in other
files under `Mathlib.Data.Option`.
Other basic operations on `Option` are defined in the core library.
-/

namespace Option

#align option.lift_or_get Option.liftOrGet

/-- Lifts a relation `α → β → Prop` to a relation `Option α → Option β → Prop` by just adding
`none ~ none`. -/
inductive rel (r : α → β → Prop) : Option α → Option β → Prop
| /-- If `a ~ b`, then `some a ~ some b` -/
  some {a b} : r a b → rel r (some a) (some b)
| /-- `none ~ none` -/
  none : rel r none none

/-- Traverse an object of `Option α` with a function `f : α → F β` for an applicative `F`. -/
protected def traverse.{u, v} {F : Type u → Type v} [Applicative F] {α β : Type _} (f : α → F β) :
  Option α → F (Option β)
| none => pure none
| some x => some <$> f x

/-- If you maybe have a monadic computation in a `[Monad m]` which produces a term of type `α`,
then there is a naturally associated way to always perform a computation in `m` which maybe
produces a result. -/
def maybe.{u, v} {m : Type u → Type v} [Monad m] {α : Type u} : Option (m α) → m (Option α)
| none => pure none
| some fn => some <$> fn

#align option.mmap Option.mapM
#align option.melim Option.elimM
#align option.mget_or_else Option.getDM

variable {α : Type _} {β : Type _}

-- Porting note: Would need to add the attribute directly in `Init.Prelude`.
-- attribute [inline] Option.isSome Option.isNone

/-- An elimination principle for `Option`. It is a nondependent version of `Option.rec`. -/
@[simp]
protected def elim' (b : β) (f : α → β) : Option α → β
  | some a => f a
  | none => b

#align option.elim Option.elim'

theorem mem_some_iff {α : Type _} {a b : α} : a ∈ some b ↔ b = a := by simp

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
      if h : p a then isTrue fun o e ↦ some_inj.1 e ▸ h
      else isFalse <| mt (fun H ↦ H _ rfl) h

instance decidableExistsMem {p : α → Prop} [DecidablePred p] :
    ∀ o : Option α, Decidable (∃ a ∈ o, p a)
  | none => isFalse fun ⟨a, ⟨h, _⟩⟩ ↦ by cases h
  | some a => if h : p a then isTrue <| ⟨_, rfl, h⟩ else isFalse fun ⟨_, ⟨rfl, hn⟩⟩ ↦ h hn

/-- Inhabited `get` function. Returns `a` if the input is `some a`, otherwise returns `default`. -/
@[reducible]
def iget [Inhabited α] : Option α → α
  | some x => x
  | none => default

theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl

@[simp]
theorem mem_toList {a : α} {o : Option α} : a ∈ toList o ↔ a ∈ o := by
  cases o <;> simp [toList, eq_comm]

#align option.mem_to_list Option.mem_toList

instance liftOrGet_isCommutative (f : α → α → α) [IsCommutative α f] :
    IsCommutative (Option α) (liftOrGet f) :=
  ⟨fun a b ↦ by cases a <;> cases b <;> simp [liftOrGet, IsCommutative.comm]⟩

instance liftOrGet_isAssociative (f : α → α → α) [IsAssociative α f] :
    IsAssociative (Option α) (liftOrGet f) :=
  ⟨fun a b c ↦ by cases a <;> cases b <;> cases c <;> simp [liftOrGet, IsAssociative.assoc]⟩

instance liftOrGet_isIdempotent (f : α → α → α) [IsIdempotent α f] :
    IsIdempotent (Option α) (liftOrGet f) :=
  ⟨fun a ↦ by cases a <;> simp [liftOrGet, IsIdempotent.idempotent]⟩

instance liftOrGet_isLeftId (f : α → α → α) : IsLeftId (Option α) (liftOrGet f) none :=
  ⟨fun a ↦ by cases a <;> simp [liftOrGet]⟩

instance liftOrGet_isRightId (f : α → α → α) : IsRightId (Option α) (liftOrGet f) none :=
  ⟨fun a ↦ by cases a <;> simp [liftOrGet]⟩

#align option.lift_or_get_comm Option.liftOrGet_isCommutative
#align option.lift_or_get_assoc Option.liftOrGet_isAssociative
#align option.lift_or_get_idem Option.liftOrGet_isIdempotent
#align option.lift_or_get_is_left_id Option.liftOrGet_isLeftId
#align option.lift_or_get_is_right_id Option.liftOrGet_isRightId
