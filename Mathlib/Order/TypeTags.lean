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

/-- Attach `⊤` to a type. -/
inductive WithTop (α : Type*) where
  | top : WithTop α
  | some (a : α) : WithTop α

/-- Attach `⊥` to a type. -/
@[to_dual existing]
inductive WithBot (α : Type*) where
  | bot : WithBot α
  | some (a : α) : WithBot α

instance WithBot.instRepr [Repr α] : Repr (WithBot α) :=
  ⟨fun o _ =>
    match o with
    | bot => "⊥"
    | some a => "↑" ++ repr a⟩

@[to_dual existing]
instance WithTop.instRepr [Repr α] : Repr (WithTop α) :=
  ⟨fun o _ =>
    match o with
    | top => "⊤"
    | some a => "↑" ++ repr a⟩

namespace WithBot

attribute [coe] WithTop.some WithBot.some

@[to_dual]
instance coe : Coe α (WithBot α) :=
  ⟨some⟩

@[to_dual]
instance : Bot (WithBot α) :=
  ⟨bot⟩

@[to_dual]
instance inhabited : Inhabited (WithBot α) :=
  ⟨⊥⟩

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
