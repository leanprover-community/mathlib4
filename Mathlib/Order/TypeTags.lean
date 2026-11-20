/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Yury Kudryashov
-/
module

public import Mathlib.Order.Notation

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Order-related type synonyms

In this file we define `WithBot` and `WithTop`.
-/

@[expose] public section

variable {α : Type*}

/-- Attach `⊥` to a type. -/
@[to_dual /-- Attach `⊤` to a type. -/]
def WithBot (α : Type*) := Option α

instance WithBot.instRepr [Repr α] : Repr (WithBot α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ repr a⟩

@[to_dual existing]
instance WithTop.instRepr [Repr α] : Repr (WithTop α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ repr a⟩

namespace WithBot

/-- The canonical map from `α` into `WithBot α` -/
@[to_dual (attr := coe, match_pattern) /-- The canonical map from `α` into `WithTop α` -/]
def some : α → WithBot α :=
  Option.some

@[to_dual]
instance coe : Coe α (WithBot α) :=
  ⟨some⟩

@[to_dual]
instance bot : Bot (WithBot α) :=
  ⟨none⟩

@[to_dual]
instance inhabited : Inhabited (WithBot α) :=
  ⟨⊥⟩

/-- Recursor for `WithBot` using the preferred forms `⊥` and `↑a`. -/
@[to_dual (attr := elab_as_elim, induction_eliminator, cases_eliminator)
/-- Recursor for `WithTop` using the preferred forms `⊤` and `↑a`. -/]
def recBotCoe {motive : WithBot α → Sort*} (bot : motive ⊥) (coe : ∀ a : α, motive a) :
    ∀ n : WithBot α, motive n
  | ⊥ => bot
  | (a : α) => coe a

@[to_dual (attr := simp)]
theorem recBotCoe_bot {motive : WithBot α → Sort*} (bot : motive ⊥) (coe : ∀ a : α, motive a) :
    recBotCoe bot coe ⊥ = bot :=
  rfl

@[to_dual (attr := simp)]
theorem recBotCoe_coe {motive : WithBot α → Sort*} (bot : motive ⊥) (coe : ∀ a : α, motive a)
    (x : α) : recBotCoe bot coe (x : WithBot α) = coe x :=
  rfl

end WithBot
