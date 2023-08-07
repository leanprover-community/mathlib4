/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Computability.Language

/-!
# Context-Free Grammar

This file contains the definition of a Context-Free Grammar (CFG), which is a grammar that has a
single nonterminal symbol on the left-hand side of each rule.
Note that derivation by a grammar is inherently nondeterministic.
-/

/-- The type of symbols is the disjoint union of terminals and nonterminals.

We do not require `T` and `N` to be finite.
As a result, we do not need to copy the typeclass instances `[Fintype T]` and `[Fintype N]`
alongside our type parameters (which would appear in almost every lemma).
Instead, later we work in terms of a list of rewrite rules, which is finite by definition and from
which we could infer that only a finite set of terminals and a finite set of nonterminals can occur.
-/
inductive Symbol (T : Type) (N : Type)
  | terminal    (t : T) : Symbol T N
  | nonterminal (n : N) : Symbol T N

/-- Context-free grammar that generates words over the alphabet `T` (a type of terminals). -/
structure CFG (T : Type) where
  nt : Type                              -- type of nonterminals
  initial : nt                           -- initial nonterminal
  rules : List (nt × List (Symbol T nt)) -- rewrite rules

variable {T : Type}

/-- One step of context-free transformation. -/
def CFG.Transforms (g : CFG T) (w₁ w₂ : List (Symbol T g.nt)) : Prop :=
  ∃ r : g.nt × List (Symbol T g.nt),
    r ∈ g.rules ∧
    ∃ u v : List (Symbol T g.nt),
      w₁ = u ++ [Symbol.nonterminal r.fst] ++ v ∧ w₂ = u ++ r.snd ++ v

/-- Any number of steps of context-free transformation. -/
def CFG.Derives (g : CFG T) : List (Symbol T g.nt) → List (Symbol T g.nt) → Prop :=
  Relation.ReflTransGen g.Transforms

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def CFG.Generates (g : CFG T) (w : List T) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w)

/-- The set of words that can be derived from the initial nonterminal. -/
def CFG.language (g : CFG T) : Language T :=
  setOf g.Generates

/-- Predicate "[language] is context-free"; defined by existence of a context-free grammar. -/
def IsCF (L : Language T) : Prop :=
  ∃ g : CFG T, g.language = L

variable {g : CFG T}

/-- The relation `CFG.Derives` is reflexive. -/
lemma CFG.deri_self {w : List (Symbol T g.nt)} :
    g.Derives w w :=
  Relation.ReflTransGen.refl

lemma CFG.deri_of_tran {v w : List (Symbol T g.nt)} (hyp : g.Transforms v w) :
    g.Derives v w :=
  Relation.ReflTransGen.single hyp

/-- The relation `CFG.Derives` is transitive. -/
lemma CFG.deri_of_deri_deri {u v w : List (Symbol T g.nt)}
    (huv : g.Derives u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  Relation.ReflTransGen.trans huv hvw

lemma CFG.deri_of_deri_tran {u v w : List (Symbol T g.nt)}
    (huv : g.Derives u v) (hvw : g.Transforms v w) :
    g.Derives u w :=
  CFG.deri_of_deri_deri huv (CFG.deri_of_tran hvw)

lemma CFG.deri_of_tran_deri {u v w : List (Symbol T g.nt)}
    (huv : g.Transforms u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  CFG.deri_of_deri_deri (CFG.deri_of_tran huv) hvw

lemma CFG.eq_or_tran_deri_of_deri {u w : List (Symbol T g.nt)} (hyp : g.Derives u w) :
    u = w  ∨  ∃ v : List (Symbol T g.nt), g.Transforms u v ∧ g.Derives v w  :=
  Relation.ReflTransGen.cases_head hyp

lemma CFG.eq_or_deri_tran_of_deri {u w : List (Symbol T g.nt)} (hyp : g.Derives u w) :
    u = w  ∨  ∃ v : List (Symbol T g.nt), g.Derives u v ∧ g.Transforms v w  :=
  (Relation.ReflTransGen.cases_tail hyp).casesOn (Or.inl ∘ Eq.symm) Or.inr
