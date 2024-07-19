/-
Copyright (c) 2023 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe
-/
import Mathlib.Computability.TMComputable

/-!
# Complexity

This file defines concepts from complexity theory related to polynomial-time computability on
Turing machines (TMs), nondeterministic polynomial-time (NP) computation (defined using efficiently
verifiable certificates), polynomial-time reductions, and NP completeness and hardness.

The file focuses on definitions. Key results remain to be filled in: computability including
existence of a univeral TM, halting problem, and Rice's Theorem (`Computability.Partrec` provide );
Cook-Levin Theorem; definition of space bounded computation; equivalence of resource bounds across
machine models (`TM0`, `TM1`, and `TM2` in `Computability.TuringMachine`); and complexity bounds
for functions in mathlib with an acceptable encoding. An extensive set of TODO items are in
comments below.

## Main Definitions

- `PolyTimeLanguages` : Predicate for languages accepted in polynomial time
- `NPLanguages`       : Predicate for languages accepted in nondeterministic polynomial time
- `PolyTimeReduction` : Computable functions that are polynomial time reductions
- `NPComplete`        : NP completeness of a language

## Implementation notes

This file draws on `Computability.TMComputable`, which defines polynomial-time computations
`TM2ComputableInPolyTime` by `FinTM2`. It focuses on computations on the type `BitString`
(`List Bool`) to enforce an acceptable encoding (i.e. not unary) when defining resource bounds.

## References

* [Arora and Barak, *Computational Complexity: A Modern Approach*][arorabarak2016]
-/

open Computability

namespace Turing

/-- Defines polynomial time functions on binary strings to binary strings -/
def isPolyTimeTM (tm : BitString → BitString) : Prop := Nonempty (@TM2ComputableInPolyTime
    BitString BitString finEncodingBitString finEncodingBitString tm)
-- TODO: Time complexity measures for TM0 and TM1. Equivalence of TM1 and TM2 polynomial time
-- TODO: Space complexity measures for TM0-2. Relation to time measures. PSPACE. NL=coNL
-- TODO: Time complexity for other types than BitStrings: ℕ, Lists, Graphs

/-- Complexity class FP: the set of functions computable in polynomial time -/
def PolyTimeTMs : Set (BitString → BitString) := {tm | isPolyTimeTM tm}

open Set

/-- The language accepted by a TM is the preimage of `true` -/
def L_M (tm : BitString → BitString) : Set BitString := preimage tm {[true]}

/-- Language in complexity class P: accepted by polynomial time TM -/
def PolyTimeLanguage (tm : PolyTimeTMs) : Set BitString := L_M tm

/-- Complexity class P: languages accepted by polynomial time TMs -/
def PolyTimeLanguages : Set (Set BitString) := {L_M tm | tm : PolyTimeTMs}

/-- A verifier for a nondeterministic polynomial time (NP) language -/
def isVerifier (tm : PolyTimeTMs) : Prop :=
  ∃ (p: Polynomial ℕ), ∀ (x certificate : BitString), (Bpair x certificate) ∈ L_M tm →
    certificate.length < p.eval x.length

/-- The set of verifiers for nondeterministic polynomial time languages -/
def verifiers : Set PolyTimeTMs := {tm | isVerifier tm}

/-- A nondeterministic polynomial time language -/
def NPLanguage (tm : verifiers) : Set BitString :=
  {x | ∃ (certificate : BitString), Bpair x certificate ∈ L_M tm}

/-- Complexity class NP: languages accepted in nondeterministic polynomial time -/
def NPLanguages : Set (Set BitString) := {NPLanguage tm| tm : verifiers}

/-- Polynomial time reduction (also known as Karp, many-to-one, or mapping) of language L1 to L2 -/
def PolyTimeReduction (tm : BitString → BitString) (L1 L2 : Set BitString) : Prop :=
tm ∈ PolyTimeTMs ∧ ∀ (x: BitString), x∈L1 ↔ tm x ∈ L2

/-- A language is NP hard if any NP language is reducible to it -/
def NPHard (L2 : Set BitString): Prop :=
  ∀ (L1 : NPLanguages), ∃ (tm : PolyTimeTMs), PolyTimeReduction tm L1 L2

/-- A language is NP complete if it is NP hard and is an NP language -/
def NPComplete (L1 : Set BitString) : Prop := NPHard L1 ∧ L1 ∈ NPLanguages

open Turing.TM2.Stmt

/-- A Turing machine computing the identity on α. -/
def acceptAll {α : Type} (ea : FinEncoding α) : FinTM2 where
  K := Unit
  k₀ := ⟨⟩
  k₁ := ⟨⟩
  Γ _ := ea.Γ
  Λ := Unit
  main := ⟨⟩
  σ := Unit
  initialState := ⟨⟩
  Γk₀Fin := ea.ΓFin
  m _ := halt


-- TODO: existence of universal TM, undecidability of halting; Rice's Theorem
-- TODO: Other definitions of NP and their equivalance
-- TODO: transitivity of PolyTimeReductions
-- TODO: If NP hard language is in P, then P=NP
-- TODO: An NP complete language is in P iff P=NP
-- TODO: Cook-Levin thm drawing on universal TM and bounded halting and THEOREMS as NP complete
-- TODO: NP completeness for other specific languages especially 3SAT
-- TODO: equivalence of complexity class P across machine models
-- TODO: Decision vs search
-- TODO: Deterministic and nondeterministic time hierarchy, space hierarchy, nonuniform
-- TODO: NP intermediate (Ladner)
-- TODO: BGS contrary relativizations
-- TODO: Space-bounded computation
-- TODO: EXP≠NEXP implies P≠NP
-- TODO: Circuit complexity, P/poly. Shannon bound
-- TODO: coNP-completeness of TAUT. NP≠coNP imples P≠NP
-- TODO: Cook Reckhow Proof systems: P Time map onto TAUT
-- TODO: Polynomial-time hierachy. Karp Lipton
-- TODO: NA, AC
-- TODO: BPP, RP, coRP, ZPP. BPP⊆P/poly. Randomized reductions
-- TODO: IP=PSPACE, NEXP=MIP
-- TODO: One-way functions, PRGs (HILL), derandomization
-- TODO: PCP theorem

end Turing
