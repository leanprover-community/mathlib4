/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.ChomskyNormalForm.Basic
import Mathlib.Computability.ChomskyNormalForm.EmptyElimination
import Mathlib.Computability.ChomskyNormalForm.UnitElimination
import Mathlib.Computability.ChomskyNormalForm.TerminalRestriction
import Mathlib.Computability.ChomskyNormalForm.LengthRestriction

/-!
# Chomsky Normal Form Translation

This file contains the algorithm to translate a `ContextFreeGrammar.` to a
`ChomskyNormalFormGrammar` by using the algorithms
`ContextFreeGrammar.eliminateEmpty` removing rules with an empty right-hand side,
`ContextFreeGrammar.eliminateUnitRules` removing rules with a single nonterminal right-hand side,
`ContextFreeGrammar.restrictTerminals` restricting all terminals to only occur as the single
symbol of a rule's right-hand side, and
`ContextFreeGrammar.restrictLength` translating `ContextFreeRule`s with multiple nonterminals to
`ChomskyNormalFormRule`s with only two nonterminals on the right-hand side.

## Main definitions
* `ContextFreeGrammar.toCNF`: Transforms a context-free grammar to a chomsky normal form grammar

## Main theorems
* `ContextFreeGrammar.toCNF_correct`: The transformed grammar's language coincides with the
original language (except for the empty string)

## References
* [John E. Hopcroft, Rajeev Motwani, and Jeffrey D. Ullman. 2006. Introduction to Automata Theory,
   Languages, and Computation (3rd Edition). Addison-Wesley Longman Publishing Co., Inc., USA.]
   [Hopcroft et al. 2006]
-/

universe uN uT

variable {T : Type uT}

namespace ContextFreeGrammar

/-- Translation of `ContextFreeGrammar` to `ChomskyNormalFormGrammar`, composing the individual
 translation passes -/
noncomputable def toCNF [DecidableEq T] (g : ContextFreeGrammar T) [DecidableEq g.NT] :
    ChomskyNormalFormGrammar T :=
  g.eliminateEmpty.eliminateUnitRules.restrictTerminals.restrictLength (e := instDecidableEqSum)

variable {g : ContextFreeGrammar T}

lemma newTerminalRules_terminal_output {r : ContextFreeRule T g.NT} :
    ∀ r' ∈ newTerminalRules r, ∃ t, r'.output = [Symbol.terminal t] := by
  simp only [newTerminalRules, List.mem_filterMap, forall_exists_index, and_imp]
  intro r' s hs
  split <;> intro hr' <;> simp only [reduceCtorEq, Option.some.injEq] at hr'
  simp [← hr']

variable [DecidableEq T] [DecidableEq g.NT]

lemma restrictTerminals_nonUnit_output (hrₒ : ∀ r ∈ g.rules, NonUnit r.output) :
    ∀ r' ∈ g.restrictTerminals.rules, NonUnit r'.output := by
  simp only [restrictTerminals, restrictTerminalRules, restrictTerminalRule, newTerminalRules,
    List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and,
    List.mem_cons, List.mem_filterMap, forall_exists_index, and_imp]
  intro r' r hrg hr'
  cases hr' with
  | inl hr' =>
    have : (∀ t : T, r.output ≠ [Symbol.terminal t]) → NonUnit (rightEmbedString r.output) :=
      rightEmbed_string_nonUnit (hrₒ _ hrg)
    aesop
  | inr hr' =>
    obtain ⟨s, ⟨_, hsr⟩⟩ := hr'
    cases s <;> simp [reduceCtorEq, Option.some.injEq] at hsr
    rw [← hsr]
    trivial

lemma restrictTerminals_not_empty_output (hne : ∀ r ∈ g.rules, r.output ≠ []) :
    ∀ r' ∈ g.restrictTerminals.rules, r'.output ≠ [] := by
  simp only [restrictTerminals, restrictTerminalRules, restrictTerminalRule, newTerminalRules,
    List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and,
    List.mem_cons, List.mem_filterMap, ne_eq, forall_exists_index, and_imp]
  intro r' r hrg hr'
  cases hr' with
  | inl =>
    aesop
  | inr hr' =>
    obtain ⟨s, ⟨_, hsr⟩⟩ := hr'
    cases s <;> simp [reduceCtorEq, Option.some.injEq] at hsr
    rw [← hsr]
    simp

lemma restrictTerminals_terminal_or_nonterminals :
    ∀ r ∈ g.restrictTerminals.rules, (∃ t, r.output = [Symbol.terminal t])
      ∨ (∀ s ∈ r.output, ∃ nt, s = Symbol.nonterminal nt) := by
  simp only [restrictTerminals, restrictTerminalRules, restrictTerminalRule, List.mem_toFinset,
    List.mem_flatten, List.mem_map, Finset.mem_toList, exists_exists_and_eq_and, List.mem_cons,
    Sum.exists, forall_exists_index, and_imp]
  intro r' r _
  split <;> intro h
  · cases h with
    | inl hr =>
      rw [hr]
      simp
    | inr hr =>
      left
      exact newTerminalRules_terminal_output r' hr
  · cases h with
    | inl hr =>
      right
      rw [hr]
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
      intro s hs
      cases s <;> tauto
    | inr hr =>
      left
      exact newTerminalRules_terminal_output r' hr

lemma eliminateUnitRules_not_empty_output (hne : ∀ r ∈ g.rules, r.output ≠ []) :
    ∀ r' ∈ g.eliminateUnitRules.rules, r'.output ≠ [] := by
  simp only [eliminateUnitRules, removeUnitRules, computeUnitPairRules, List.mem_toFinset,
    List.mem_flatten, List.mem_map, Finset.mem_toList, Prod.exists, ne_eq,
    forall_exists_index, and_imp]
  intro r _ _ _ _ hg
  rw [← hg]
  simp only [List.mem_filterMap, Finset.mem_toList, Option.ite_none_right_eq_some,
    forall_exists_index, and_imp]
  intro _ hrg _
  split
  · simp
  · simp only [Option.some.injEq]
    intro hr
    rw [← hr]
    apply hne _ hrg

lemma eliminateEmpty_not_empty_output : ∀ r ∈ g.eliminateEmpty.rules, r.output ≠ [] := by
  simp only [eliminateEmpty]
  intro r hrg
  exact output_mem_removeNullables hrg

lemma eliminateUnitRules_output_nonUnit : ∀ r ∈ g.eliminateUnitRules.rules, NonUnit r.output := by
  simp only [eliminateUnitRules, removeUnitRules, computeUnitPairRules, List.mem_toFinset,
    List.mem_flatten, List.mem_map, Finset.mem_toList, Prod.exists, forall_exists_index, and_imp]
  intro r l n₁ n₂ _ hl hrl
  rw [← hl] at hrl
  simp only [List.mem_filterMap, Finset.mem_toList, Option.ite_none_right_eq_some] at hrl
  obtain ⟨_, _, _, hr⟩ := hrl
  split at hr
  · contradiction
  · simp only [Option.some_inj] at hr
    rw [← hr]
    unfold NonUnit
    split <;> tauto

theorem toCNF_correct : g.language \ {[]} = g.toCNF.language := by
  unfold toCNF
  rw [eliminateEmpty_correct, eliminateUnitRules_correct, restrictTerminals_correct,
    restrictLength_correct (e := instDecidableEqSum)]
  intro r hrg
  match hrₒ : r.output with
  | [] =>
    exfalso
    exact restrictTerminals_not_empty_output
      (eliminateUnitRules_not_empty_output eliminateEmpty_not_empty_output) _ hrg hrₒ
  | [Symbol.terminal _] =>
    cases r; simp only at hrₒ; rw [hrₒ]
    constructor
  | [Symbol.nonterminal _] =>
    exfalso
    apply restrictTerminals_nonUnit_output at hrg
    · rw [hrₒ] at hrg
      contradiction
    · exact eliminateUnitRules_output_nonUnit
  | _ :: _ :: _ =>
    cases r
    apply restrictTerminals_terminal_or_nonterminals at hrg
    cases hrg <;> rename_i hrg
    · obtain ⟨t, ht⟩ := hrg
      rw [ht] at hrₒ
      simp at hrₒ
    · rw [hrₒ] at hrg
      simp only [List.mem_cons, forall_eq_or_imp] at hrg
      obtain ⟨n₁, hn₁⟩ := hrg.1
      obtain ⟨n₂, hn₂⟩ := hrg.2.1
      dsimp only at hrₒ
      rw [hrₒ, hn₁, hn₂]
      constructor
      · simp only [List.length_cons, Nat.le_add_left]
      · intro s hs
        cases hs with
        | head => constructor
        | tail _ hs =>
          cases hs with
          | head => constructor
          | tail _ hs =>
            obtain ⟨_, hs⟩ := hrg.2.2 s hs
            rw [hs]
            constructor

end ContextFreeGrammar
