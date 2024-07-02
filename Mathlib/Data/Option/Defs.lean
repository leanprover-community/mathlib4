/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

#align_import data.option.defs from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

/-!
# Extra definitions on `Option`

This file defines more operations involving `Option α`. Lemmas about them are located in other
files under `Mathlib.Data.Option`.
Other basic operations on `Option` are defined in the core library.
-/

namespace Option

#align option.lift_or_get Option.liftOrGet

/-- Traverse an object of `Option α` with a function `f : α → F β` for an applicative `F`. -/
protected def traverse.{u, v}
    {F : Type u → Type v} [Applicative F] {α : Type*} {β : Type u} (f : α → F β) :
    Option α → F (Option β)
  | none => pure none
  | some x => some <$> f x
#align option.traverse Option.traverse

#align option.maybe Option.sequence

#align option.mmap Option.mapM
#align option.melim Option.elimM
#align option.mget_or_else Option.getDM

variable {α : Type*} {β : Type*}

-- Porting note: Would need to add the attribute directly in `Init.Prelude`.
-- attribute [inline] Option.isSome Option.isNone

/-- An elimination principle for `Option`. It is a nondependent version of `Option.rec`. -/
protected def elim' (b : β) (f : α → β) : Option α → β
  | some a => f a
  | none => b
#align option.elim Option.elim'

@[simp]
theorem elim'_none (b : β) (f : α → β) : Option.elim' b f none = b := rfl
@[simp]
theorem elim'_some {a : α} (b : β) (f : α → β) : Option.elim' b f (some a) = f a := rfl

-- Porting note: this lemma was introduced because it is necessary
-- in `CategoryTheory.Category.PartialFun`
lemma elim'_eq_elim {α β : Type*} (b : β) (f : α → β) (a : Option α) :
    Option.elim' b f a = Option.elim a b f := by
  cases a <;> rfl


theorem mem_some_iff {α : Type*} {a b : α} : a ∈ some b ↔ b = a := by simp
#align option.mem_some_iff Option.mem_some_iff

/-- `o = none` is decidable even if the wrapped type does not have decidable equality.
This is not an instance because it is not definitionally equal to `Option.decidableEq`.
Try to use `o.isNone` or `o.isSome` instead.
-/
@[inline]
def decidableEqNone {o : Option α} : Decidable (o = none) :=
  decidable_of_decidable_of_iff isNone_iff_eq_none
#align option.decidable_eq_none Option.decidableEqNone

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
abbrev iget [Inhabited α] : Option α → α
  | some x => x
  | none => default
#align option.iget Option.iget

theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl
#align option.iget_some Option.iget_some

@[simp]
theorem mem_toList {a : α} {o : Option α} : a ∈ toList o ↔ a ∈ o := by
  cases o <;> simp [toList, eq_comm]
#align option.mem_to_list Option.mem_toList

instance liftOrGet_isCommutative (f : α → α → α) [Std.Commutative f] :
    Std.Commutative (liftOrGet f) :=
  ⟨fun a b ↦ by cases a <;> cases b <;> simp [liftOrGet, Std.Commutative.comm]⟩

instance liftOrGet_isAssociative (f : α → α → α) [Std.Associative f] :
    Std.Associative (liftOrGet f) :=
  ⟨fun a b c ↦ by cases a <;> cases b <;> cases c <;> simp [liftOrGet, Std.Associative.assoc]⟩

instance liftOrGet_isIdempotent (f : α → α → α) [Std.IdempotentOp f] :
    Std.IdempotentOp (liftOrGet f) :=
  ⟨fun a ↦ by cases a <;> simp [liftOrGet, Std.IdempotentOp.idempotent]⟩

instance liftOrGet_isId (f : α → α → α) : Std.LawfulIdentity (liftOrGet f) none where
  left_id a := by cases a <;> simp [liftOrGet]
  right_id a := by cases a <;> simp [liftOrGet]

#align option.lift_or_get_comm Option.liftOrGet_isCommutative
#align option.lift_or_get_assoc Option.liftOrGet_isAssociative
#align option.lift_or_get_idem Option.liftOrGet_isIdempotent
#align option.lift_or_get_is_left_id Option.liftOrGet_isId
#align option.lift_or_get_is_right_id Option.liftOrGet_isId

/-- Convert `undef` to `none` to make an `LOption` into an `Option`. -/
def _root_.Lean.LOption.toOption {α} : Lean.LOption α → Option α
  | .some a => some a
  | _ => none
