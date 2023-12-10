/-
Copyright (c) 2023 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe (and others to be added)
-/
import Mathlib.Computability.Encoding
import Mathlib.Computability.TMComputable
import Mathlib.Computability.Language
import Mathlib.Data.Polynomial.Eval

/-!
# Complexity

This file defines basic concepts in complexity theory of polynomial-time computability, polynomial
reductions, nondeterministic polynomial time, and NP completeness and hardness.

This file is schematic as several key elements remain to be filled in: existence of a univeral TM;
noncomputability of halting, and Rice's Theorem (see `Computability.Partrec`); Cook-Levin Theorem,
especially NP Completeness of 3SAT; definition of space bounded computation; equivalence of
polynomially-bounded computation as defined in the three models `TM0`, `TM1`, and `TM2` in
`Computability.TuringMachine`, and complexity bounds for a multitude of computations throughout
mathlib, given a selected model and an acceptable encoding. An extensive set of  TODO items are
noted in the body below.

## Main Definitions

- `PolyTimeLanguages` : Predicate for languages accepted in polynomial time
- `NPLanguages`       : Predicate for languages accepted in nondeterministic polynomial time
- `PolyTimeReduction` : Computable functions that are polynomial time reductions
- `NPComplete`        : NP completeness of a language

## Implementation notes

This file draws on `Computability.TMComputable`, which defines polynomial-time computations by
`FinTM2`.

## References

* [Arora and Barak, *Arora and Barak*][arorabarak2016]
-/

open Computability

namespace Turing

/-- Defines polynomial time function of a type, assuming an acceptable coding the input type e.g.
not unary -/
def isPolyTimeFunctionByType {α β: Type} {ea : FinEncoding α} {eb : FinEncoding β}
    (f : α → β) : Prop := Nonempty (@TM2ComputableInPolyTime α β ea eb f)
-- TODO: Time complexity for other types than BitStrings: ℕ, Lists, Graphs, with required use of
-- Acceptable coding. Time complexity of number functions throughout mathlib

/-- Defines polynomial time functions on binary strings to binary strings -/
def isPolyTimeTM (tm : BitString → BitString) : Prop :=
    Nonempty (@TM2ComputableInPolyTime BitString BitString finEncodingBitString finEncodingBitString tm)
-- TODO: Time complexity measures for TM0 and TM1. Equivalence of TM1 and TM2 polynomial time
-- TODO: Space complexity measures for TM0-2. Relation to time measures. PSPACE. NL=coNL

/-- Complexity class FP: the set of functions computable in polynomial time -/
def PolyTimeTMs : Set (BitString → BitString) := {tm | isPolyTimeTM tm}

open Set

/-- The language accepted by a TM is the preimage of `true` -/
def L_M (tm : BitString → BitString) : Set BitString := preimage tm {[true]}

/-- Language in complexity class P: accepted by polynomial time TM -/
def PolyTimeLanguage (tm : PolyTimeTMs) : Set BitString := L_M tm

/-- Complexity class P: languages accepted by polynomial time TMs -/
def PolyTimeLanguages : Set (Set BitString) := {L_M tm | tm : PolyTimeTMs}

/-- A verifier for a nondeterministic polynomial time language -/
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
-- TODO: Other definitions of NP and their equivalance

/-- Polynomial time reduction (also known as Karp-reducible, many-to-one reducible, or mapping
reducible) -/
def PolyTimeReduction (tm : BitString → BitString) (L1 L2 : Set BitString) : Prop :=
tm ∈ PolyTimeTMs ∧ ∀ (x: BitString), x∈L1 ↔ tm x ∈ L2
-- TODO: transitivity of PolyTimeReductions

/-- A language is NP hard if any NP language is reducible to it -/
def NPHard (L1 : Set BitString): Prop :=
  ∀ (L2 : NPLanguages), ∃ (tm : PolyTimeTMs), PolyTimeReduction tm L1 L2
-- If NP hard language is in P, then P=NP

/-- A language is NP complete if it is NP hard and is an NP language -/
def NPComplete (L1 : Set BitString) : Prop := NPHard L1 ∧ L1 ∈ NPLanguages
-- TODO: An NP complete language is in P iff P=NP
-- TODO: Cook-Levin drawing on universal TM and bounded halting and THEOREMS as NP complete
-- TODO: NP completeness for other specific languages especially 3SAT
-- TODO: Decision vs search
-- TODO: Deterministic and nondeterministic time hierarchy, space hierarchy, nonuniform
-- TODO: NP intermediate (Ladner)
-- TODO: BGS contrary relativizations
-- TODO: EXP≠NEXP implies P≠NP
-- TODO: Circuit complexity, P/poly. Shannon bound
-- TODO: coNP-completeness of TAUT. NP≠coNP imples P≠NP
-- TODO: Cook Reckhow Proof systems: P Time map onto TAUT
-- TODO: Polynomial-time hierachy. Karp Lipton
-- TODO: NA, AC
-- TODO: BPP, RP, coRP, ZPP. BPP⊆P/poly. Randomized reductions
-- TODO: IP=PSPACE, NEXP=MIP, NEXP=PCP[poly,poly4]
-- TODO: One-way functions, PRGs, derandomization

end Turing
