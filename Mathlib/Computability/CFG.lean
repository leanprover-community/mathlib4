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
Derivation by a grammar is inherently nondeterministic.
-/

universe u

/--
The type of symbols is the disjoint union of terminals `T` and nonterminals `N`.
We do not require `T` and `N` to be finite in this definition.
As a result, we do not need to copy the typeclass instances `[Fintype T]` and `[Fintype N]`
alongside our type parameters (which would appear in almost every lemma).
Instead, later we work in terms of a list of rewrite rules, which is finite by definition and from
which we could infer that only a finite set of terminals and a finite set of nonterminals can occur.
-/
inductive Symbol (T : Type u) (N : Type u)
  | terminal    (t : T) : Symbol T N
  | nonterminal (n : N) : Symbol T N

/-- Context-free grammar that generates words over the alphabet `T` (a type of terminals). -/
structure CFG (T : Type _) where
  nt : Type _                            -- type of nonterminals
  initial : nt                           -- initial nonterminal
  rules : List (nt × List (Symbol T nt)) -- rewrite rules

namespace CFG

variable {T : Type u}

/-- One step of context-free transformation. -/
def Transforms (g : CFG T) (w₁ w₂ : List (Symbol T g.nt)) : Prop :=
  ∃ r : g.nt × List (Symbol T g.nt),
    r ∈ g.rules ∧
    ∃ u v : List (Symbol T g.nt),
      w₁ = u ++ [Symbol.nonterminal r.fst] ++ v ∧ w₂ = u ++ r.snd ++ v

/-- Any number of steps of context-free transformation. -/
def Derives (g : CFG T) : List (Symbol T g.nt) → List (Symbol T g.nt) → Prop :=
  Relation.ReflTransGen g.Transforms

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def Generates (g : CFG T) (w : List T) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w)

/-- The set of words that can be derived from the initial nonterminal. -/
def language (g : CFG T) : Language T :=
  setOf g.Generates

/-- Predicate "[language] is context-free"; defined by existence of a context-free grammar. -/
def _root_.Language.IsCF (L : Language T) : Prop :=
  ∃ g : CFG T, g.language = L

variable {g : CFG T}

lemma Transforms.single {v w : List (Symbol T g.nt)} (hvw : g.Transforms v w) :
    g.Derives v w :=
  Relation.ReflTransGen.single hvw

@[refl]
lemma Derives.refl {w : List (Symbol T g.nt)} :
    g.Derives w w :=
  Relation.ReflTransGen.refl

@[trans]
lemma Derives.derives {u v w : List (Symbol T g.nt)}
    (huv : g.Derives u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  Relation.ReflTransGen.trans huv hvw

lemma Derives.transforms {u v w : List (Symbol T g.nt)}
    (huv : g.Derives u v) (hvw : g.Transforms v w) :
    g.Derives u w :=
  huv.derives hvw.single

lemma Transforms.derives {u v w : List (Symbol T g.nt)}
    (huv : g.Transforms u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  huv.single.derives hvw

lemma Derives.eq_or_head {u w : List (Symbol T g.nt)} (huw : g.Derives u w) :
    u = w ∨ ∃ v : List (Symbol T g.nt), g.Transforms u v ∧ g.Derives v w :=
  Relation.ReflTransGen.cases_head huw

lemma Derives.eq_or_tail {u w : List (Symbol T g.nt)} (huw : g.Derives u w) :
    u = w ∨ ∃ v : List (Symbol T g.nt), g.Derives u v ∧ g.Transforms v w :=
  (Relation.ReflTransGen.cases_tail huw).casesOn (Or.inl ∘ Eq.symm) Or.inr
