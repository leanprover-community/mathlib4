/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Yury Kudryashov
-/
import Mathlib.Order.Notation

/-!
# Order-related type synonyms

In this file we define `WithBot`, `WithTop`, `ENat`, and `PNat`.
The definitions were moved to this file without any theory
so that, e.g., `Data/Countable/Basic` can prove `Countable ENat`
without exploding its imports.
-/

variable {α : Type*}

/-- Attach `⊥` to a type. -/
inductive WithBot (α : Type*) where
  | bot : WithBot α
  /- TODO: rename to `coe`:
  this is only called `some` because of the historical implementation via `Option`. -/
  /-- The canonical map from `α` into `WithBot α` -/
  | some : α → WithBot α

namespace WithBot

instance [Repr α] : Repr (WithBot α) :=
  ⟨fun o _ =>
    match o with
    | .bot => "⊥"
    | .some a => "↑" ++ repr a⟩

attribute [coe] some

instance coe : Coe α (WithBot α) :=
  ⟨some⟩

instance instBot : Bot (WithBot α) :=
  ⟨bot⟩

instance inhabited : Inhabited (WithBot α) :=
  ⟨⊥⟩

@[simp, grind _=_] theorem bot_eq : (bot : WithBot α) = ⊥ := rfl

/-- Recursor for `WithBot` using the preferred forms `⊥` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recBotCoe {C : WithBot α → Sort*} (bot : C ⊥) (coe : ∀ a : α, C a) : ∀ n : WithBot α, C n
  | ⊥ => bot
  | (a : α) => coe a

@[simp]
theorem recBotCoe_bot {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) :
    @recBotCoe _ C d f ⊥ = d :=
  rfl

@[simp]
theorem recBotCoe_coe {C : WithBot α → Sort*} (d : C ⊥) (f : ∀ a : α, C a) (x : α) :
    @recBotCoe _ C d f ↑x = f x :=
  rfl

end WithBot

--TODO(Mario): Construct using order dual on `WithBot`
/-- Attach `⊤` to a type. -/
def WithTop (α : Type*) := WithBot α

namespace WithTop

/-- The canonical map from `α` into `WithTop α` -/
@[coe, match_pattern] def some : α → WithTop α :=
  WithBot.some

@[match_pattern] def top : WithTop α :=
  WithBot.bot

instance [Repr α] : Repr (WithTop α) :=
  ⟨fun o _ =>
    match o with
    | .top => "⊤"
    | .some a => "↑" ++ repr a⟩

instance coeTC : CoeTC α (WithTop α) :=
  ⟨some⟩

instance instTop : Top (WithTop α) :=
  ⟨top⟩

instance inhabited : Inhabited (WithTop α) :=
  ⟨⊤⟩

@[simp, grind =] theorem top_eq : (top : WithTop α) = ⊤ := rfl

/-- Recursor for `WithTop` using the preferred forms `⊤` and `↑a`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
def recTopCoe {C : WithTop α → Sort*} (top : C ⊤) (coe : ∀ a : α, C a) : ∀ n : WithTop α, C n
  | .top => top
  | .some a => coe a

@[simp]
theorem recTopCoe_top {C : WithTop α → Sort*} (d : C ⊤) (f : ∀ a : α, C a) :
    @recTopCoe _ C d f ⊤ = d :=
  rfl

@[simp]
theorem recTopCoe_coe {C : WithTop α → Sort*} (d : C ⊤) (f : ∀ a : α, C a) (x : α) :
    @recTopCoe _ C d f ↑x = f x :=
  rfl

end WithTop
