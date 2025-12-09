/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Yury Kudryashov
-/
module

public import Mathlib.Order.Notation

/-!
# Order-related type synonyms

In this file we define `WithBot` and `WithTop`.
-/

@[expose] public section

variable {α : Type*}

/-- An auxiliary structure, common to `WithBot` and `WithTop`, which guarantees that both are
def-eq.

In the future, we probably want to get rid of this, and simply use the `to_dual` tactic to dualize
theorems from one type to the other. -/
inductive WithBotTop (α : Type*) where
  | bot : WithBotTop α
  /- TODO: rename to `coe`:
  this is only called `some` because of the historical implementation via `Option`. -/
  /-- The canonical map from `α` into `WithBotTop α` -/
  | some : α → WithBotTop α

/-- Attach `⊤` to a type. -/
@[to_dual]
def WithBot (α : Type*) := WithBotTop α

instance WithBot.instRepr [Repr α] : Repr (WithBot α) :=
  ⟨fun o _ =>
    match o with
    | .bot => "⊥"
    | .some a => "↑" ++ repr a⟩

@[to_dual existing]
instance WithTop.instRepr [Repr α] : Repr (WithTop α) :=
  ⟨fun o _ =>
    match o with
    | .bot => "⊤"
    | .some a => "↑" ++ repr a⟩

namespace WithBot

/-- The canonical map from `α` into `WithBot α` -/
@[to_dual (attr := coe, match_pattern)]
def some : α → WithBot α :=
  WithBotTop.some

@[to_dual (attr := match_pattern)]
def bot : WithBot α :=
  WithBotTop.bot

@[to_dual]
instance coe : Coe α (WithBot α) :=
  ⟨some⟩

@[to_dual]
instance instBot : Bot (WithBot α) :=
  ⟨bot⟩

@[to_dual]
instance inhabited : Inhabited (WithBot α) :=
  ⟨⊥⟩

@[to_dual (attr := simp, grind =)]
theorem bot_eq : (bot : WithBot α) = ⊥ := rfl

/-- Recursor for `WithBot` using the preferred forms `⊥` and `↑a`. -/
@[to_dual (attr := elab_as_elim, induction_eliminator, cases_eliminator)
/-- Recursor for `WithTop` using the preferred forms `⊤` and `↑a`. -/]
def recBotCoe {C : WithBot α → Sort*} (bot : C ⊥) (coe : ∀ a : α, C a) : ∀ n : WithBot α, C n
  | ⊥ => bot
  | (a : α) => coe a

@[to_dual (attr := simp)]
theorem recBotCoe_bot {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) :
    @recBotCoe _ C d f ⊥ = d :=
  rfl

@[to_dual (attr := simp)]
theorem recBotCoe_coe {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) (x : α) :
    @recBotCoe _ C d f ↑x = f x :=
  rfl

end WithBot
