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

variable {α β : Type*}

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

/-- Returns `true` on `some x` and false on `⊥`. -/
@[to_dual /-- Returns `true` on `some x` and false on `⊤`. -/]
def isSome : WithBot α → Bool
  | ⊥ => false
  | (_ : α) => true

@[to_dual (attr := simp)]
lemma isSome_bot : isSome (⊥ : WithBot α) = false := rfl

@[to_dual (attr := simp)]
lemma isSome_some (x : α) : isSome (x : WithBot α) = true := rfl

@[to_dual (attr := simp)]
theorem isSome_dite {p : Prop} {_ : Decidable p} {b : p → α} :
    (if h : p then some (b h) else ⊥).isSome = true ↔ p := by
  split <;> simpa

@[to_dual (attr := simp)]
theorem isSome_ite {p : Prop} {_ : Decidable p} {b : α} :
    (if p then some b else ⊥).isSome = true ↔ p := by
  split <;> simpa

@[to_dual (attr := simp)]
theorem isSome_dite' {p : Prop} {_ : Decidable p} {b : ¬ p → α} :
    (if h : p then ⊥ else some (b h)).isSome = true ↔ ¬ p := by
  split <;> simpa

@[to_dual (attr := simp)]
theorem isSome_ite' {p : Prop} {_ : Decidable p} {b : α} :
    (if p then ⊥ else some b).isSome = true ↔ ¬ p := by
  split <;> simpa

end WithBot
