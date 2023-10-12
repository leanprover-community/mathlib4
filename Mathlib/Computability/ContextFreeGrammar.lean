/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Computability.Language

/-!
# Context-Free Grammar

This file contains the definition of a Context-Free Grammar, which is a grammar that has a single
nonterminal symbol on the left-hand side of each rule.
-/

universe uT uN in
/-- Rule that rewrites a single nonterminal to any list of symbols. -/
structure ContextFreeRule (T : Type uT) (N : Type uN) where
  /-- Input nonterminal a.k.a. left-hand side -/
  input : N
  /-- Output string a.k.a. right-hand side -/
  output : List (Symbol T N)

-- the `uN` universe comes first as it can't be inferred
/-- Context-free grammar that generates words over the alphabet `T` (a type of terminals). -/
structure ContextFreeGrammar.{uN,uT} (T : Type uT) where
  /-- Type of nonterminals -/
  NT : Type uN
  /-- Initial nonterminal -/
  initial : NT
  /-- Rewrite rules -/
  rules : List (ContextFreeRule T NT)

universe uT uN
variable {T : Type uT} {N : Type uN}

/-- One application of single context-free rule. -/
inductive ContextFreeRule.RewritesTo (r : ContextFreeRule T N) :
    List (Symbol T N) → List (Symbol T N) → Prop
  /-- The replacement is at the start of the remaining string. -/
  | head (s : List (Symbol T N)) :
      r.RewritesTo (Symbol.nonterminal r.input :: s) (r.output ++ s)
  /-- There is a replacement later in the string. -/
  | cons (x : Symbol T N) {s₁ s₂ : List (Symbol T N)} (hrs : RewritesTo r s₁ s₂) :
      r.RewritesTo (x :: s₁) (x :: s₂)

lemma ContextFreeRule.RewritesTo.exists_parts {r : ContextFreeRule T N}
    {u v : List (Symbol T N)} (hyp : r.RewritesTo u v) :
    ∃ p : List (Symbol T N), ∃ q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q := by
  induction hyp with
  | head xs =>
    use [], xs
    simp
  | cons x _ ih =>
    rcases ih with ⟨p', q', rfl, rfl⟩
    use x :: p', q'
    simp

lemma ContextFreeRule.rewritesTo_of_exists_parts
    (r : ContextFreeRule T N) (p q : List (Symbol T N)) :
    r.RewritesTo (p ++ [Symbol.nonterminal r.input] ++ q) (p ++ r.output ++ q) := by
  induction p with
  | nil         => exact ContextFreeRule.RewritesTo.head q
  | cons d l ih => exact ContextFreeRule.RewritesTo.cons d ih

theorem ContextFreeRule.rewritesTo_iff {r : ContextFreeRule T N}
    (u v : List (Symbol T N)) :
    r.RewritesTo u v ↔
      ∃ p : List (Symbol T N), ∃ q : List (Symbol T N),
        u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q :=
  ⟨fun t ↦ t.exists_parts, by rintro ⟨p, q, rfl, rfl⟩; apply rewritesTo_of_exists_parts⟩

namespace ContextFreeGrammar

/-- If `g` is a context-free grammar, `g.Produces u v` means that one step of context-free
    transformation sends `u` to `v`. -/
def Produces (g : ContextFreeGrammar.{uN} T) (u v : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, r.RewritesTo u v

/-- Any number of steps of context-free transformation. -/
abbrev Derives (g : ContextFreeGrammar.{uN} T) :
    List (Symbol T g.NT) → List (Symbol T g.NT) → Prop :=
  Relation.ReflTransGen g.Produces

/-- String `s` can be derived by grammar `g` from its initial nonterminal. -/
def Generates (g : ContextFreeGrammar.{uN} T) (s : List (Symbol T g.NT)) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] s

/-- The set of words that can be derived from the initial nonterminal. -/
def language (g : ContextFreeGrammar.{uN} T) : Language T :=
  { w | g.Generates (List.map Symbol.terminal w) }

@[simp]
lemma mem_language_iff (g : ContextFreeGrammar.{uN} T) (w : List T) :
    w ∈ g.language ↔ g.Derives [Symbol.nonterminal g.initial] (List.map Symbol.terminal w) := by
  rfl

variable {g : ContextFreeGrammar.{uN} T}

@[refl]
lemma Derives.refl (w : List (Symbol T g.NT)) : g.Derives w w :=
  Relation.ReflTransGen.refl

lemma Produces.single {v w : List (Symbol T g.NT)} (hvw : g.Produces v w) : g.Derives v w :=
  Relation.ReflTransGen.single hvw

@[trans]
lemma Derives.trans {u v w : List (Symbol T g.NT)} (huv : g.Derives u v) (hvw : g.Derives v w) :
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
