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
(`initial_state`), a start symbol (`start_symbol`), a set of final states (`final_states`), a
transition function (`transition_fun`), and a proof that, for any input, the transition function
returns a finite set as output. -/
structure PDA (Q T S : Type) [Fintype Q] [Fintype T] [Fintype S] where
  /-- Initial state. -/
  initialState : Q
  /-- Start symbol on the stack. -/
  startSymbol : S
  /-- Set of final states. -/
  finalStates : Set Q
  /-- Transition function reading a letter from `T` if present and an epsilon otherwise. -/
  transitionFun : Q → Option T → S → Set (Q × List S)
  finite_transitionFun (q : Q) (x : Option T) (Z : S) : (transitionFun q x Z).Finite

namespace PDA

variable {Q T S : Type} [Fintype Q] [Fintype T] [Fintype S]

/-- A configuration of a PDA is a state (`state`), the remaining input (`input`), and the current
  stack. -/
@[ext]
structure Conf (p : PDA Q T S) where
  /-- Current state. -/
  state : Q
  /-- Remaining input. -/
  input : List T
  /-- Current stack. -/
  stack : List S

variable {M : PDA Q T S}

/-- `Reaches₁ r₁ r₂` means that `r₂` is reachable from `r₁` in one step. -/
def Reaches₁ (r₁ r₂ : Conf M) : Prop :=
  ∃ (Z : S) (α : List S) (β : List S), r₁.stack = Z :: α ∧ r₂.stack = β ++ α ∧ (
    r₁.input = r₂.input ∧ (r₂.state, β) ∈ M.transitionFun r₁.state none Z ∨
    ∃ (a : T), r₁.input = a :: r₂.input ∧ (r₂.state, β) ∈ (M.transitionFun r₁.state (some a) Z)
  )

/-- `Reaches r₁ r₂` means that `r₂` is reachable from `r₁` in finitely many steps. -/
def Reaches : Conf M → Conf M → Prop := Relation.ReflTransGen Reaches₁

/-- `acceptsByEmptyStack M` is the language accepted by the PDA `M` based on the empty-stack
  condition. -/
def acceptsByEmptyStack (M : PDA Q T S) : Language T :=
  { w : List T | ∃ q : Q,
      Reaches (⟨M.initialState, w, [M.startSymbol]⟩ : Conf M) ⟨q, [], []⟩ }

/-- `acceptsByFinalState M` is the language accepted by the PDA `M` based on the final-state
  condition. -/
def acceptsByFinalState (M : PDA Q T S) : Language T :=
  { w : List T | ∃ q ∈ M.finalStates, ∃ γ : List S,
      Reaches (⟨M.initialState, w, [M.startSymbol]⟩ : Conf M) ⟨q, [], γ⟩ }

end PDA
