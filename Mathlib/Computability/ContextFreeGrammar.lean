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

/--
The type of symbols is the disjoint union of terminals `T` and nonterminals `N`.
-/
inductive Symbol (T : Type _) (N : Type _)
  /-- Terminal symbols (of the same type as the language) -/
  | terminal    (t : T) : Symbol T N
  /-- Nonterminal symbols (must not be present at the end of word being generated) -/
  | nonterminal (n : N) : Symbol T N

structure ContextFreeRule (T : Type _) (N : Type _) where
  input : N
  output : List (Symbol T N)

/-- Context-free grammar that generates words over the alphabet `T` (a type of terminals). -/
structure ContextFreeGrammar (T : Type _) where
  /-- Type of nonterminals -/
  NT : Type _
  /-- Initial nonterminal -/
  initial : NT
  /-- Rewrite rules -/
  rules : List (ContextFreeRule T NT)

variable {T : Type _}

inductive ContextFreeRule.RewritesTo {N : Type _} (r : ContextFreeRule T N) :
    List (Symbol T N) → List (Symbol T N) → Prop
  /-- The replacement is at the start of the remaining string. -/
  | head (xs : List (Symbol T N)) :
      r.RewritesTo (Symbol.nonterminal r.input :: xs) (r.output ++ xs)
  /-- There is a replacement later in the string. -/
  | cons (x : Symbol T N) {s₁ s₂ : List (Symbol T N)} (h : RewritesTo r s₁ s₂) :
      r.RewritesTo (x :: s₁) (x :: s₂)

namespace ContextFreeGrammar

/-- One step of context-free transformation. -/
def Produces (g : ContextFreeGrammar T) (u v : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, ContextFreeRule.RewritesTo r u v

/-- Any number of steps of context-free transformation. -/
def Derives (g : ContextFreeGrammar T) : List (Symbol T g.NT) → List (Symbol T g.NT) → Prop :=
  Relation.ReflTransGen g.Produces

/-- Accepts a word (a list of terminals) iff it can be derived from the initial nonterminal. -/
def Generates (g : ContextFreeGrammar T) (w : List T) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w)

/-- The set of words that can be derived from the initial nonterminal. -/
def language (g : ContextFreeGrammar T) : Language T :=
  setOf g.Generates

variable {g : ContextFreeGrammar T}

@[refl]
lemma Derives.refl {w : List (Symbol T g.NT)} :
    g.Derives w w :=
  Relation.ReflTransGen.refl

lemma Produces.single {v w : List (Symbol T g.NT)} (hvw : g.Produces v w) :
    g.Derives v w :=
  Relation.ReflTransGen.single hvw

@[trans]
lemma Derives.trans {u v w : List (Symbol T g.NT)}
    (huv : g.Derives u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  Relation.ReflTransGen.trans huv hvw

lemma Derives.trans_produces {u v w : List (Symbol T g.NT)}
    (huv : g.Derives u v) (hvw : g.Produces v w) :
    g.Derives u w :=
  huv.trans hvw.single

lemma Produces.trans_derives {u v w : List (Symbol T g.NT)}
    (huv : g.Produces u v) (hvw : g.Derives v w) :
    g.Derives u w :=
  huv.single.trans hvw

lemma Derives.eq_or_head {u w : List (Symbol T g.NT)} (huw : g.Derives u w) :
    u = w ∨ ∃ v : List (Symbol T g.NT), g.Produces u v ∧ g.Derives v w :=
  Relation.ReflTransGen.cases_head huw

lemma Derives.eq_or_tail {u w : List (Symbol T g.NT)} (huw : g.Derives u w) :
    u = w ∨ ∃ v : List (Symbol T g.NT), g.Derives u v ∧ g.Produces v w :=
  (Relation.ReflTransGen.cases_tail huw).casesOn (Or.inl ∘ Eq.symm) Or.inr
