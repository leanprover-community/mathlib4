/-
Copyright (c) 2024 Alexander Loitzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl
-/

import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Computability.ChomskyNormalForm.UnitElimination

/-!
# Terminal Restriction

This file contains the algorithm to restrict rules to either rewrite to a single terminal or only
nonterminals.

## Main definitions
* `ContextFreeGrammar.restrictTerminals`: Removes all rules which do not rewrite to a single
  terminal or nonterminals only. Adds corresponding rules to preserve the language.

## Main theorems
* `ContextFreeGrammar.restrictTerminals_correct`: The transformed grammar's language coincides with
  the original

## References
* [John E. Hopcroft, Rajeev Motwani, and Jeffrey D. Ullman. 2006. Introduction to Automata Theory,
   Languages, and Computation (3rd Edition). Addison-Wesley Longman Publishing Co., Inc., USA.]
   [Hopcroft et al. 2006]
-/

universe uN uT
variable {T : Type uT}

/-! Definitions of embeding into and projecting to the type of symbols of the new grammar -/
section EmbedProject

variable {N : Type uN}

/-- Intuitive embedding of symbols of the original grammar into symbols of the new grammar's type -/
def embedSymbol : Symbol T N → Symbol T (N ⊕ T)
  | .terminal t => .terminal t
  | .nonterminal n => .nonterminal (.inl n)

/-- Intuitive embedding of strings of the original grammar into strings of the new grammar's type -/
abbrev embedString (u : List (Symbol T N)) : List (Symbol T (N ⊕ T)) := u.map embedSymbol

/-- Embedding of symbols of the original grammar into nonterminals of the new grammar -/
def rightEmbedSymbol : Symbol T N → Symbol T (N ⊕ T)
  | .terminal t => .nonterminal (.inr t)
  | .nonterminal n => .nonterminal (.inl n)

/-- Embedding of strings of the original grammar into nonterminal (symbol) strings of the new
grammar -/
abbrev rightEmbedString (w : List (Symbol T N)) := w.map rightEmbedSymbol

/-- Projection from symbols of the new grammars type into symbols of the original grammar -/
def projectSymbol : Symbol T (N ⊕ T) → Symbol T N
  | .terminal t => .terminal t
  | .nonterminal (.inl nt) => .nonterminal nt
  | .nonterminal (.inr t) => .terminal t

/-- Projection from strings of the new grammars type into strings of the original grammar -/
def projectString (u : List (Symbol T (N ⊕ T))) : List (Symbol T N) := u.map projectSymbol

@[simp]
lemma embedSymbol_nonterminal_eq {nt : N} :
    embedSymbol (.nonterminal nt) = (.nonterminal (.inl nt) : Symbol T (N ⊕ T)):= by
  rfl

lemma projectString_rightEmbedString_id {u : List (Symbol T N)} :
    projectString (rightEmbedString u) = u := by
  induction u with
  | nil => rfl
  | cons a =>
    simp only [rightEmbedString, projectString, List.map_cons, List.map_map, List.cons.injEq]
    constructor
    · cases a <;> rfl
    · rwa [← List.map_map]

lemma projectString_terminal_list {u : List T} :
    projectString (u.map .terminal : List (Symbol T (N ⊕ T))) = u.map .terminal := by
  induction u with
  | nil => rfl
  | cons _ _ ih =>
    simp only [projectString, List.map_map, List.map_inj_left, Function.comp_apply, List.map_cons,
      List.cons.injEq] at ih ⊢
    exact ⟨rfl, ih⟩

lemma projectSymbol_nonterminal {n : N} :
    projectSymbol (.nonterminal (.inl n) : Symbol T (N ⊕ T) ) = .nonterminal n :=
  rfl

lemma embedString_preserves_nonempty {u : List (Symbol T N)} (hu: u ≠ []) :
    embedString u ≠ [] := by
  aesop

lemma embedString_terminal_list {u : List T} :
    embedString (u.map .terminal : List (Symbol T N)) = u.map .terminal := by
  cases u with
  | nil => rfl
  | cons => simp [embedString, embedSymbol]

lemma embedString_append {u v : List (Symbol T N)} :
    embedString (u ++ v) = embedString u ++ embedString v :=
  List.map_append embedSymbol u v

lemma rightEmbed_string_nonUnit {u : List (Symbol T N)} (hu : ContextFreeGrammar.NonUnit u)
    (hut : ∀ t, u ≠ [.terminal t]) :
    ContextFreeGrammar.NonUnit (rightEmbedString u) :=
  match u with
  | [] => trivial
  | [.nonterminal _] => hu
  | [.terminal t] => hut t rfl
  | _ :: _ :: _ => by simp [ContextFreeGrammar.NonUnit]

end EmbedProject

namespace ContextFreeGrammar

/-! ### Definition of `ContextFreeGrammar.restrictTerminals`, the algorithm to restrict rules s.t.
terminals occur only as the single symbol at the right-hand side of a rule. -/
section RestrictTerminals

/-- Computes rules r' : T -> t, for all terminals t occuring in `r.output`-/
def newTerminalRules {N : Type*} (r : ContextFreeRule T N) : List (ContextFreeRule T (N ⊕ T)) :=
  let terminal_rule (s : Symbol T N) : Option (ContextFreeRule T (N ⊕ T)) :=
    match s with
    | .terminal t => some ⟨.inr t, [.terminal t]⟩
    | .nonterminal _ => none
  r.output.filterMap terminal_rule

/-- If `r.output` is a single terminal, we lift the rule to the new grammar, otherwise add new rules
for each terminal symbol in `r.output` and right-lift the rule, i.e., replace all terminals with
nonterminals -/
def restrictTerminalRule {N : Type*} (r : ContextFreeRule T N) : List (ContextFreeRule T (N ⊕ T)) :=
  (match r.output with
  | [.terminal t] => ⟨.inl r.input, [.terminal t]⟩
  | _ => ⟨.inl r.input, rightEmbedString r.output⟩
  ) :: newTerminalRules r

/-- Compute all lifted rules -/
noncomputable def restrictTerminalRules {N : Type*} [DecidableEq T] [DecidableEq N]
    (l : List (ContextFreeRule T N)) : Finset (ContextFreeRule T (N ⊕ T)) :=
  (l.map restrictTerminalRule).flatten.toFinset

/-- Construct new grammar, using the lifted rules. Each rule's output is either a single terminal
or only nonterminals -/
noncomputable def restrictTerminals [DecidableEq T] (g : ContextFreeGrammar.{uN, uT} T)
    [DecidableEq g.NT] :=
  ContextFreeGrammar.mk (g.NT ⊕ T) (.inl g.initial) (restrictTerminalRules g.rules.toList)

end RestrictTerminals

variable {g : ContextFreeGrammar.{uN, uT} T}

lemma restrictTerminalRule_right_terminal_output {t : T} {r : ContextFreeRule T g.NT}
    {r' : ContextFreeRule T (g.NT ⊕ T)} (hrr : r' ∈ restrictTerminalRule r)
    (hrt : r'.input = .inr t) :
    r'.output = [.terminal t] := by
  simp only [restrictTerminalRule, List.mem_cons] at hrr
  cases hrr <;> rename_i hrr
  · split at hrr <;> rw [hrr] at hrt <;> simp at hrt
  · simp only [newTerminalRules, List.mem_filterMap] at hrr
    obtain ⟨s, _, hsr⟩ := hrr
    cases s <;> simp only [Option.some.injEq, reduceCtorEq] at hsr
    rw [← hsr] at hrt ⊢
    simp only [Sum.inr.injEq, List.cons.injEq, Symbol.terminal.injEq, and_true] at hrt ⊢
    exact hrt

lemma restrictTerminalRules_right_terminal_output [DecidableEq T] [DecidableEq g.NT] {t : T}
    {r : ContextFreeRule T (g.NT ⊕ T)} (hrg : r ∈ restrictTerminalRules g.rules.toList)
    (hrt : r.input = .inr t) :
    r.output = [.terminal t] := by
  simp only [restrictTerminalRules, List.mem_toFinset, List.mem_flatten, List.mem_map,
    Finset.mem_toList, exists_exists_and_eq_and] at hrg
  obtain ⟨_, _, hr⟩ := hrg
  exact restrictTerminalRule_right_terminal_output hr hrt

lemma restrictTerminalRule_left {n : g.NT} {r : ContextFreeRule T g.NT}
    {r' : ContextFreeRule T (g.NT ⊕ T)} (hrr : r' ∈ restrictTerminalRule r)
    (hrn : r'.input = .inl n) :
    r.input = n ∧ r.output = projectString r'.output := by
  simp only [restrictTerminalRule, List.mem_cons] at hrr
  cases hrr <;> rename_i hrr
  · split at hrr <;> rw [hrr] at hrn ⊢ <;> simp only [Sum.inl.injEq] at hrn ⊢
    · rename_i hrt
      simp only [projectString, projectSymbol, List.map_cons, List.map_nil]
      exact ⟨hrn, hrt⟩
    · exact ⟨hrn, projectString_rightEmbedString_id ▸ rfl⟩
  · simp only [newTerminalRules, List.mem_filterMap] at hrr
    obtain ⟨r'', _, hrr⟩ := hrr
    cases r'' <;> simp only [Option.some.injEq, reduceCtorEq] at hrr
    rw [← hrr] at hrn
    tauto

lemma terminal_mem_newTerminalRules {t : T} {r : ContextFreeRule T g.NT}
    (htr : .terminal t ∈ r.output) :
    ⟨.inr t, [.terminal t]⟩ ∈ newTerminalRules r :=
  List.mem_filterMap.2 ⟨.terminal t, ⟨htr, rfl⟩⟩

variable [DecidableEq T] [DecidableEq g.NT]

lemma restrictTerminalsRules_left {n : g.NT} {r' : ContextFreeRule T (g.NT ⊕ T)}
    (hrg : r' ∈ restrictTerminalRules g.rules.toList) (hrn : r'.input = .inl n) :
    ∃ r ∈ g.rules, r.input = n ∧ r.output = projectString r'.output := by
  unfold restrictTerminalRules at hrg
  simp only [restrictTerminalRules, List.mem_toFinset, List.mem_flatten, List.mem_map,
    Finset.mem_toList, exists_exists_and_eq_and] at hrg
  obtain ⟨r, hrg, hrr⟩ := hrg
  exact ⟨r, hrg, restrictTerminalRule_left hrr hrn⟩

lemma restrictTerminals_produces_derives_projectString {u v : List (Symbol T (g.NT ⊕ T))}
    (huv : (restrictTerminals g).Produces u v) :
    g.Derives (projectString u) (projectString v) := by
  obtain ⟨r', hrg', huv⟩ := huv
  obtain ⟨_, _, hu, hv⟩ := huv.exists_parts
  cases hr' : r'.input with
  | inl =>
    obtain ⟨r, hrg, hrᵢ, hrₒ⟩ := restrictTerminalsRules_left hrg' hr'
    rw [hu, hv, hr']
    unfold projectString at hrₒ ⊢
    repeat rw [List.map_append]
    exact ((Produces.append_left ⟨r, hrg, hrₒ ▸ hrᵢ ▸ .input_output⟩ _).append_right _).single
  | inr =>
    rw [hu, hv, hr', restrictTerminalRules_right_terminal_output hrg' hr']
    simp only [projectString, List.map_append]
    rfl

lemma restrictTerminals_derives_derives_projectString {u v : List (Symbol T (g.NT ⊕ T))}
    (huv : (restrictTerminals g).Derives u v) :
    g.Derives (projectString u) (projectString v) := by
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih => exact (restrictTerminals_produces_derives_projectString hp).trans ih

lemma restrictTerminals_derives_rightEmbedString_embedString {u : List (Symbol T g.NT)}
    (hu : ∀ t, (.terminal t) ∈ u → ∃ r ∈ g.rules, (.terminal t) ∈ r.output) :
    (restrictTerminals g).Derives (rightEmbedString u) (embedString u) := by
  induction u with
  | nil => rfl
  | cons a _ ih =>
    simp only [List.mem_cons, List.map_cons] at hu ⊢
    rw [← List.singleton_append, ← @List.singleton_append _ (embedSymbol a)]
    apply Derives.append_left_trans
    · apply ih
      intro t ht
      exact hu t (.inr ht)
    · cases a with
      | nonterminal => rfl
      | terminal t =>
        specialize hu t
        simp only [true_or, forall_const] at hu
        obtain ⟨r, hrg, htr⟩ := hu
        apply Produces.single
        constructor
        constructor
        · apply List.subset_def.1; swap
          · exact terminal_mem_newTerminalRules htr
          · simp only [restrictTerminals, restrictTerminalRules, restrictTerminalRule]
            intro r' hrr
            simp only [List.mem_dedup, List.mem_flatten, List.mem_map, Finset.mem_toList,
              exists_exists_and_eq_and]
            exact ⟨r, hrg, by right; exact hrr⟩
        · exact .input_output

lemma derives_restrictTerminals_derives_embedString {u v : List (Symbol T g.NT)}
    (huv : g.Derives u v) :
    (restrictTerminals g).Derives (embedString u) (embedString v) := by
  induction huv using Derives.head_induction_on with
  | refl => rfl
  | head hp _ ih =>
    obtain ⟨r, hrg, hr⟩ := hp
    apply Derives.trans _ ih
    obtain ⟨_, _, heq₁, heq₂⟩ := hr.exists_parts
    rw [heq₁, heq₂]
    repeat rw [embedString_append]
    refine Derives.append_right (Derives.append_left ?_ _) _
    by_cases hrt : ∃ t, r.output = [.terminal t]
    · obtain ⟨t, hrt⟩ := hrt
      refine Produces.single ⟨⟨.inl r.input, [.terminal t]⟩, ⟨?_, ?_⟩⟩
      · unfold restrictTerminals restrictTerminalRules restrictTerminalRule
        simp only [List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList,
          exists_exists_and_eq_and]
        use r, hrg
        simp [hrt]
      · rw [hrt]
        simp only [List.map_cons, List.map_nil]
        exact .input_output
    · apply Produces.trans_derives
      · refine ⟨⟨.inl r.input, rightEmbedString r.output⟩, ⟨?_, ?_⟩⟩
        · simp only [restrictTerminals, restrictTerminalRules, restrictTerminalRule,
            List.mem_toFinset, List.mem_flatten, List.mem_map, Finset.mem_toList,
            exists_exists_and_eq_and]
          use r, hrg
          split <;> rename_i heq
          · rename_i t'
            exfalso
            exact hrt ⟨t', heq⟩
          · simp
        · unfold embedString embedSymbol
          simp only [List.map_cons, List.map_nil]
          exact .input_output
      · apply restrictTerminals_derives_rightEmbedString_embedString
        intros
        use r

theorem restrictTerminals_correct : g.language = g.restrictTerminals.language := by
  apply Set.eq_of_subset_of_subset <;>
    intro w hw <;>
      rw [mem_language_iff] at hw ⊢
  · apply derives_restrictTerminals_derives_embedString at hw
    rwa [embedString_terminal_list] at hw
  · apply restrictTerminals_derives_derives_projectString at hw
    rw [projectString_terminal_list] at hw
    unfold restrictTerminals projectString at hw
    rwa [List.map_cons, List.map_nil, projectSymbol_nonterminal] at hw

end ContextFreeGrammar
