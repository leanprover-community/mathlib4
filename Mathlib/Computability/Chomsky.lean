/-
Copyright (c) 2024 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Computability.DFA
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Fintype.Prod

/-!
# Chomsky hierarchy

This file attempts to capture the Chomsky hierarchy. We want to show inclusions between classes
of languages: Regular ⊆ ContextFree ⊆ ContextSensitive ⊆ RecursivelyEnumerable

## Main theorems
* `Language.IsRegular.isContextFree`: Every regular language is context-free.
-/

variable {α σ : Type*} [Fintype α] [Fintype σ]

/-- Convert a finite DFA to a context-free grammar. -/
noncomputable def DFA.toContextFreeGrammar (M : DFA α σ) [DecidablePred M.accept] :
    ContextFreeGrammar α where
  NT := σ
  initial := M.start
  rules :=
    Finset.univ.map ⟨fun x : σ × α =>
      ⟨x.1, [Symbol.terminal x.2, Symbol.nonterminal (M.step x.1 x.2)]⟩, fun _ => by simp⟩
    /-∪
    (Finset.univ.filter M.accept).map ⟨fun s : σ => ⟨s, []⟩, fun _ => by simp⟩-/

lemma DFA.toContextFreeGrammar_produces (M : DFA α σ) [DecidablePred M.accept]
    (w : List (Symbol α σ)) (s : σ) (a : α) :
    M.toContextFreeGrammar.Produces (w ++ [Symbol.nonterminal s])
      (w ++ [Symbol.terminal a, Symbol.nonterminal (M.step s a)]) := by
  apply ContextFreeGrammar.Produces.append_left
  use ⟨s, [Symbol.terminal a, Symbol.nonterminal (M.step s a)]⟩
  constructor
  · simp [DFA.toContextFreeGrammar]
  apply ContextFreeRule.Rewrites.head

lemma DFA.toContextFreeGrammar_derives (M : DFA α σ) [DecidablePred M.accept]
    (p : List (Symbol α σ)) (s : σ) (w : List α) :
    M.toContextFreeGrammar.Derives (p ++ [Symbol.nonterminal s])
      (p ++ w.map Symbol.terminal ++ [Symbol.nonterminal (M.evalFrom s w)]) := by
  induction w using List.list_reverse_induction with
  | base => simp [ContextFreeGrammar.Derives.refl]
  | ind d l ih =>
    apply ih.trans_produces
    simp only [List.append_assoc, List.map_append, evalFrom_append_singleton]
    apply ContextFreeGrammar.Produces.append_left
    apply DFA.toContextFreeGrammar_produces

lemma DFA.toContextFreeGrammar_generates (M : DFA α σ) [DecidablePred M.accept] (w : List α) :
    M.toContextFreeGrammar.Generates
      (w.map Symbol.terminal ++ [Symbol.nonterminal (M.eval w)]) :=
  M.toContextFreeGrammar_derives [] M.start w

lemma DFA.toContextFreeGrammar_mem_language {M : DFA α σ} [DecidablePred M.accept] {w : List α} :
    w ∈ M.toContextFreeGrammar.language ↔ w ∈ M.accepts := by
  rw [ContextFreeGrammar.mem_language_iff, mem_accepts]
  sorry

theorem Language.IsRegular.isContextFree {L : Language α} (hL : L.IsRegular) : L.IsContextFree := by
  classical
  obtain ⟨_, _, M, rfl⟩ := hL
  use M.toContextFreeGrammar
  ext w
  exact M.toContextFreeGrammar_mem_language
