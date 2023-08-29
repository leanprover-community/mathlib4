/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init.Algebra.Classes

#align_import data.option.defs from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

/-!
# Extra definitions on `Option`

This file defines more operations involving `Option α`. Lemmas about them are located in other
files under `Mathlib.Data.Option`.
Other basic operations on `Option` are defined in the core library.
-/

set_option autoImplicit true

namespace Option

#align option.lift_or_get Option.liftOrGet

/-- Lifts a relation `α → β → Prop` to a relation `Option α → Option β → Prop` by just adding
`none ~ none`. -/
inductive rel (r : α → β → Prop) : Option α → Option β → Prop
  | /-- If `a ~ b`, then `some a ~ some b` -/
    some {a b} : r a b → rel r (some a) (some b)
  | /-- `none ~ none` -/
    none : rel r none none
#align option.rel Option.rel

/-- Traverse an object of `Option α` with a function `f : α → F β` for an applicative `F`. -/
protected def traverse.{u, v} {F : Type u → Type v} [Applicative F] {α β : Type _} (f : α → F β) :
    Option α → F (Option β)
  | none => pure none
  | some x => some <$> f x
#align option.traverse Option.traverse

/-- If you maybe have a monadic computation in a `[Monad m]` which produces a term of type `α`,
then there is a naturally associated way to always perform a computation in `m` which maybe
produces a result. -/
def maybe.{u, v} {m : Type u → Type v} [Monad m] {α : Type u} : Option (m α) → m (Option α)
  | none => pure none
  | some fn => some <$> fn
#align option.maybe Option.maybe

#align option.mmap Option.mapM
#align option.melim Option.elimM

@[deprecated getDM]
protected def getDM' [Monad m] (x : m (Option α)) (y : m α) : m α := do
  (← x).getDM y
#align option.mget_or_else Option.getDM'

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
theorem elim'_some (b : β) (f : α → β) : Option.elim' b f (some a) = f a := rfl

-- porting note: this lemma was introduced because it is necessary
-- in `CategoryTheory.Category.PartialFun`
lemma elim'_eq_elim {α β : Type*} (b : β) (f : α → β) (a : Option α) :
    Option.elim' b f a = Option.elim a b f := by
  cases a <;> rfl
  -- ⊢ Option.elim' b f none = Option.elim none b f
              -- 🎉 no goals
              -- 🎉 no goals


theorem mem_some_iff {α : Type*} {a b : α} : a ∈ some b ↔ b = a := by simp
                                                                      -- 🎉 no goals
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
                       -- 🎉 no goals
  | some a =>
      if h : p a then isTrue fun o e ↦ some_inj.1 e ▸ h
      else isFalse <| mt (fun H ↦ H _ rfl) h

instance decidableExistsMem {p : α → Prop} [DecidablePred p] :
    ∀ o : Option α, Decidable (∃ a ∈ o, p a)
  | none => isFalse fun ⟨a, ⟨h, _⟩⟩ ↦ by cases h
                                         -- 🎉 no goals
  | some a => if h : p a then isTrue <| ⟨_, rfl, h⟩ else isFalse fun ⟨_, ⟨rfl, hn⟩⟩ ↦ h hn

/-- Inhabited `get` function. Returns `a` if the input is `some a`, otherwise returns `default`. -/
@[reducible]
def iget [Inhabited α] : Option α → α
  | some x => x
  | none => default
#align option.iget Option.iget

theorem iget_some [Inhabited α] {a : α} : (some a).iget = a :=
  rfl
#align option.iget_some Option.iget_some

@[simp]
theorem mem_toList {a : α} {o : Option α} : a ∈ toList o ↔ a ∈ o := by
  cases o <;> simp [toList, eq_comm]
  -- ⊢ a ∈ toList none ↔ a ∈ none
              -- 🎉 no goals
              -- 🎉 no goals
#align option.mem_to_list Option.mem_toList

instance liftOrGet_isCommutative (f : α → α → α) [IsCommutative α f] :
    IsCommutative (Option α) (liftOrGet f) :=
  ⟨fun a b ↦ by cases a <;> cases b <;> simp [liftOrGet, IsCommutative.comm]⟩
                -- ⊢ liftOrGet f none b = liftOrGet f b none
                            -- ⊢ liftOrGet f none none = liftOrGet f none none
                            -- ⊢ liftOrGet f (some val✝) none = liftOrGet f none (some val✝)
                                        -- 🎉 no goals
                                        -- 🎉 no goals
                                        -- 🎉 no goals
                                        -- 🎉 no goals

instance liftOrGet_isAssociative (f : α → α → α) [IsAssociative α f] :
    IsAssociative (Option α) (liftOrGet f) :=
  ⟨fun a b c ↦ by cases a <;> cases b <;> cases c <;> simp [liftOrGet, IsAssociative.assoc]⟩
                  -- ⊢ liftOrGet f (liftOrGet f none b) c = liftOrGet f none (liftOrGet f b c)
                              -- ⊢ liftOrGet f (liftOrGet f none none) c = liftOrGet f none (liftOrGet f none c)
                              -- ⊢ liftOrGet f (liftOrGet f (some val✝) none) c = liftOrGet f (some val✝) (lift …
                                          -- ⊢ liftOrGet f (liftOrGet f none none) none = liftOrGet f none (liftOrGet f non …
                                          -- ⊢ liftOrGet f (liftOrGet f none (some val✝)) none = liftOrGet f none (liftOrGe …
                                          -- ⊢ liftOrGet f (liftOrGet f (some val✝) none) none = liftOrGet f (some val✝) (l …
                                          -- ⊢ liftOrGet f (liftOrGet f (some val✝¹) (some val✝)) none = liftOrGet f (some  …
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals
                                                      -- 🎉 no goals

instance liftOrGet_isIdempotent (f : α → α → α) [IsIdempotent α f] :
    IsIdempotent (Option α) (liftOrGet f) :=
  ⟨fun a ↦ by cases a <;> simp [liftOrGet, IsIdempotent.idempotent]⟩
              -- ⊢ liftOrGet f none none = none
                          -- 🎉 no goals
                          -- 🎉 no goals

instance liftOrGet_isLeftId (f : α → α → α) : IsLeftId (Option α) (liftOrGet f) none :=
  ⟨fun a ↦ by cases a <;> simp [liftOrGet]⟩
              -- ⊢ liftOrGet f none none = none
                          -- 🎉 no goals
                          -- 🎉 no goals

instance liftOrGet_isRightId (f : α → α → α) : IsRightId (Option α) (liftOrGet f) none :=
  ⟨fun a ↦ by cases a <;> simp [liftOrGet]⟩
              -- ⊢ liftOrGet f none none = none
                          -- 🎉 no goals
                          -- 🎉 no goals

#align option.lift_or_get_comm Option.liftOrGet_isCommutative
#align option.lift_or_get_assoc Option.liftOrGet_isAssociative
#align option.lift_or_get_idem Option.liftOrGet_isIdempotent
#align option.lift_or_get_is_left_id Option.liftOrGet_isLeftId
#align option.lift_or_get_is_right_id Option.liftOrGet_isRightId
