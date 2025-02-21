/-
Copyright (c) 2025 Stefan Hetzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Leichtfried, Stefan Hetzl
-/
import Mathlib.Computability.Language

/-!
# Pushdown Automata

This file contains the definition of a Pushdown Automaton (PDA). Pushdown automata recognize
exactly the context-free languages.
-/

/-- A PDA is a set of states (`Q`), a tape alphabet (`T`), a stack alphabet (`S`),  an inital state
  (`initial_state`), a start symbol (`start_symbol`), a set of final states (`final_states`), and a
  transition function. The transition function is given in two parts: `transition_fun` reads a
  letter and `transition_fun'` makes an epsilon transition. -/
structure PDA (Q T S : Type) [Fintype Q] [Fintype T] [Fintype S] where
  initial_state : Q
  start_symbol : S
  final_states : Set Q
  transition_fun : Q → T → S → Set (Q × List S)
  transition_fun' : Q → S → Set (Q × List S)
  finite (q : Q)(a : T)(Z : S): (transition_fun q a Z).Finite
  finite' (q : Q)(Z : S): (transition_fun' q Z).Finite

namespace PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

@[ext]
structure conf (p : PDA Q T S) where
  state : Q
  input : List T
  stack : List S

variable {pda : PDA Q T S}

def step (r₁ : conf pda) : Set (conf pda) :=
  match r₁ with
    | ⟨q, a::w, Z::α⟩ =>
        { r₂ : conf pda | ∃ (p : Q) (β : List S), (p,β) ∈ pda.transition_fun q a Z ∧
                          r₂ = ⟨p, w, (β ++ α)⟩ } ∪
        { r₂ : conf pda | ∃ (p : Q) (β : List S), (p,β) ∈ pda.transition_fun' q Z ∧
                          r₂ = ⟨p, a :: w, (β ++ α)⟩ }
    | ⟨q, [], Z::α⟩ => { r₂ : conf pda | ∃ (p : Q) (β : List S), (p,β) ∈ pda.transition_fun' q Z ∧
                                          r₂ = ⟨p, [], (β ++ α)⟩ }
    | ⟨_, _, []⟩ => ∅

def Reaches₁ (r₁ r₂ : conf pda) : Prop := r₂ ∈ step r₁
def Reaches : conf pda → conf pda → Prop := Relation.ReflTransGen Reaches₁

def acceptsByEmptyStack (pda : PDA Q T S) : Language T :=
  { w : List T | ∃ q : Q,
      Reaches (⟨pda.initial_state, w, [pda.start_symbol]⟩ : conf pda) ⟨q, [], []⟩ }

def acceptsByFinalState (pda : PDA Q T S) : Language T :=
  { w : List T | ∃ q  ∈ pda.final_states, ∃ γ : List S,
      Reaches (⟨pda.initial_state, w, [pda.start_symbol]⟩ : conf pda) ⟨q, [], γ⟩ }

end PDA
