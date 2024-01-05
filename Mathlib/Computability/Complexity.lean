/-
Copyright (c) 2023 Hunter Monroe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hunter Monroe
-/
import Mathlib.Computability.TMComputable

/-!
# Complexity

This file defines the complexity class P, that is, a set for which some Turing machine (TM) can
decide in a polynomial number of steps whether an input is a member of the set.

## Main Definitions

- `PolyTimeLanguages` : Predicate for languages accepted in polynomial time

## Implementation notes

This file draws on `Computability.TMComputable`, which defines polynomial-time computations
`TM2ComputableInPolyTime` by `FinTM2`.

## References

* [Arora and Barak, *Computational Complexity: A Modern Approach*][arorabarak2016]
-/

open Computability

namespace Turing

/-- Defines polynomial time functions on binary strings to binary strings -/
def isPolyTimeTM (tm : BitString → BitString) : Prop := Nonempty (@TM2ComputableInPolyTime
    BitString BitString finEncodingBitString finEncodingBitString tm)

/- thm: FP is closed under composition -/
/- p-/

/-- Complexity class FP: the set of functions computable in polynomial time -/
def PolyTimeTMs : Set (BitString → BitString) := {tm | isPolyTimeTM tm}

open Set

/-- The language accepted by a TM is the preimage of `true` -/
def L_M (tm : BitString → BitString) : Set BitString := preimage tm {[true]}

/-- Language in complexity class P: accepted by polynomial time TM -/
def PolyTimeLanguage (tm : PolyTimeTMs) : Set BitString := L_M tm

/-- Complexity class P: languages accepted by polynomial time TMs -/
def PolyTimeLanguages : Set (Set BitString) := {L_M tm | tm : PolyTimeTMs}

open Turing.TM2.Stmt

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
