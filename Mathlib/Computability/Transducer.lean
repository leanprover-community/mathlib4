/-
Copyright (c) 2023 Sam v. Gool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sam v. Gool
-/
import Mathlib.Computability.Language
import Mathlib.Data.Rel

/-!
# Transducers

This file defines a notion of *transducer* in the sense of Büchi, their semantics, and how
they can be composed.

## Main declarations

TODO

## Motivation

TODO

## Implementation notes

TODO

## References

* [Gastin]

## Tags

-/

open Set Computability

namespace Transducer

universe u v

def stream (A : Type u) := ℕ → A

/-- A transducer consists of a type `state` together with a transition relation
between states and letters from the input alphabet `A`, a labeling function `out`
from edges in the transition relation to the output alphabet `B`,
a starting state `start` and a set of sets of accepting states. This is a *generalized Büchi*
transducer in the sense of [Gastin].-/
structure Transducer (A B : Type u) where
  state : Type v
  transition : A → Rel state state
  out {a : A} {q₁ q₂ : state} (e : transition a q₁ q₂) : B
  start : state
  final : Set (Set state)

variable {A B C : Type u}
/-- A run of a transducer `T` on a stream `w ∈ stream A`  consists of a function `stateAt` which
    records the state of the transducer at time `t ∈ ℕ`, together with the initial condition
   `initialCond` that the run starts in the start state, the condition `transitionCond` that the
   run follows the transition relation, and the condition `finalCond` that the run visits each
   of the final sets infinitely often. -/
structure Run (T : Transducer A B) (wᵢ : stream A) where
  stateAt : stream T.state
  initialCond : stateAt 0 = T.start
  transitionCond : ∀t, T.transition (wᵢ t) (stateAt t) (stateAt (t+1))
  finalCond : ∀ F ∈ T.final, ∀ t, ∃t' ≥ t, stateAt t ∈ F

/-- The output of a run `r` of a transducer is the sequence of outputs of transitions of the run. -/
def output {T : Transducer A B} {wᵢ : stream A} (r : Run T wᵢ) (t : ℕ) :=
  T.out (r.transitionCond t)

/-- The semantics of a transducer `T` is the relation which relates a stream `u` to a stream `v`
    if, and only if, `v` is the output of a run of `T` on `u`.-/
def semantics (T : Transducer A B) : Rel (stream A) (stream B) :=
  λ u v ↦ ∃ r : Run T u, output r = v

section Composition

def compose (T₁ : Transducer A B) (T₂ : Transducer B C) : Transducer A C :=
  { state := T₁.state × T₂.state
    transition := fun a ↦ fun (p₁,p₂) ↦ fun (q₁,q₂) ↦
      ∃ (e : T₁.transition a p₁ q₁), T₂.transition (T₁.out e) p₂ q₂
    out := by
      intro _ _ _ htrans
      exact T₂.out (htrans.2)
    start := (T₁.start, T₂.start)
    final := by sorry}

theorem compose_correct : ∀ (T₁ : Transducer A B) (T₂ : Transducer B C),
semantics (compose T₁ T₂) = Rel.comp (semantics T₁) (semantics T₂) :=
by sorry
