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

/-- A PDA is a set of states (`Q`), a tape alphabet (`T`), a stack alphabet (`S`), an initial state
  (`initial_state`), a start symbol (`start_symbol`), a set of final states (`final_states`), and a
  transition function. The transition function is given in two parts: `transition_fun` reads a
  letter and `transition_fun'` makes an epsilon transition. -/
structure PDA (Q T S : Type) [Fintype Q] [Fintype T] [Fintype S] where
  /-- Initial state. -/
  initial_state : Q
  /-- Start symbol on the stack. -/
  start_symbol : S
  /-- Set of final states. -/
  final_states : Set Q
  /-- Transition function reading a letter from T. -/
  transition_fun : Q → T → S → Set (Q × List S)
  /-- Epsilon transition function. -/
  transition_fun' : Q → S → Set (Q × List S)
  finite (q : Q)(a : T)(Z : S): (transition_fun q a Z).Finite
  finite' (q : Q)(Z : S): (transition_fun' q Z).Finite

namespace PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A configuration of a PDA is a state (`state`), the remaining input (`input`), and the current
  stack. -/
@[ext]
structure conf (p : PDA Q T S) where
  /-- Current state. -/
  state : Q
  /-- Remaining input. -/
  input : List T
  /-- Current stack. -/
  stack : List S

variable {pda : PDA Q T S}

/-- `step r₁` is the set of configurations reachable from `r₁` in one step. -/
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

/-- `Reaches₁ r₁ r₂` means that `r₂` is reachable from `r₁` in one step. -/
def Reaches₁ (r₁ r₂ : conf pda) : Prop := r₂ ∈ step r₁

/-- `Reaches r₁ r₂` means that `r₂` is reachable from `r₁` in finitely many steps. -/
def Reaches : conf pda → conf pda → Prop := Relation.ReflTransGen Reaches₁

/-- `acceptsByEmptyStack pda` is the language accepted by the PDA `pda` based on the empty-stack
  condition. -/
def acceptsByEmptyStack (pda : PDA Q T S) : Language T :=
  { w : List T | ∃ q : Q,
      Reaches (⟨pda.initial_state, w, [pda.start_symbol]⟩ : conf pda) ⟨q, [], []⟩ }

/-- `acceptsByFinalState pda` is the language accepted by the PDA `pda` based on the final-state
  condition. -/
def acceptsByFinalState (pda : PDA Q T S) : Language T :=
  { w : List T | ∃ q  ∈ pda.final_states, ∃ γ : List S,
      Reaches (⟨pda.initial_state, w, [pda.start_symbol]⟩ : conf pda) ⟨q, [], γ⟩ }

end PDA
