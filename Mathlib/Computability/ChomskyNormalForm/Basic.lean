/-
Copyright (c) 2024 Alexander Loitzl, Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Loitzl, Martin Dvorak
-/

import Mathlib.Computability.ContextFreeGrammar

/-!
# Chomsky Normal Form Grammars

This file contains the definition of a chomsky normal form grammar, which is a context-free grammar
with syntactic restriction on the rules. Each rule either rewrites to a single terminal symbol or a
pair of nonterminals.

## Main definitions
* `ChomskyNormalFormGrammar`: A chomsky normal form grammar.
* `ChomskyNormalFormGrammar.toCFG`: simple translation to a context-free grammar.

## Main theorems
* `Language.toCFG_correct`: `g.toCFG` generates the same language a a context-free grammar `g`.
-/

/-- Rule that rewrites a single nonterminal to a single terminal or a pair of nonterminals. -/
inductive ChomskyNormalFormRule.{uT,uN} (T : Type uT) (N : Type uN)
  /-- First kind of rule, rewriting a nonterminal `n` to a single terminal `t`. -/
  | leaf (n : N) (t : T) : ChomskyNormalFormRule T N
  /-- Second kind of rule,  rewriting a nonterminal `n` to a pair of nonterminal `lr`. -/
  | node (n l r : N) : ChomskyNormalFormRule T N
deriving DecidableEq

/-- Chomsky normal form grammar that generates words over the alphabet `T` (a type of terminals). -/
structure ChomskyNormalFormGrammar.{uN,uT} (T : Type uT) where
  /-- Type of nonterminals. -/
  NT : Type uN
  /-- Initial nonterminal. -/
  initial : NT
  /-- Rewrite rules. -/
  rules : Finset (ChomskyNormalFormRule T NT)

universe uT uN
variable {T : Type uT}

namespace ChomskyNormalFormRule
variable {N : Type uN} {r : ChomskyNormalFormRule T N} {u v : List (Symbol T N)}

/-- The input of a CNF rule, similar to `ContextFreeRule.input` -/
@[simp]
def input (r : ChomskyNormalFormRule T N) :=
  match r with
  | leaf n _ => n
  | node n _ _ => n

/-- The output of a CNF rule, similar to `ContextFreeRule.output` -/
@[simp]
def output (r : ChomskyNormalFormRule T N) :=
  match r with
  | leaf _ t => [Symbol.terminal t]
  | node _ n₁ n₂ => [Symbol.nonterminal n₁, Symbol.nonterminal n₂]

/-- Inductive definition of a single application of a given cnf rule `r` to a string `u`;
`r.Rewrites u v` means that the `r` sends `u` to `v` (there may be multiple such strings `v`). -/
inductive Rewrites : (ChomskyNormalFormRule T N) → List (Symbol T N) → List (Symbol T N) → Prop
  /-- The replacement is at the start of the remaining string and the rule is a leaf rule. -/
  | head_leaf (n : N) (t : T) (s : List (Symbol T N)) :
      Rewrites (leaf n t) (Symbol.nonterminal n :: s) (Symbol.terminal t :: s)
  /-- The replacement is at the start of the remaining string and the rule is a node rule. -/
  | head_node (nᵢ n₁ n₂ : N) (s : List (Symbol T N)) :
      Rewrites (node nᵢ n₁ n₂) (Symbol.nonterminal nᵢ :: s)
      (Symbol.nonterminal n₁ :: Symbol.nonterminal n₂ :: s)
  /-- The replacement is at the start of the remaining string. -/
  | cons (r : ChomskyNormalFormRule T N) (s : Symbol T N) {u₁ u₂ : List (Symbol T N)}
      (hru : Rewrites r u₁ u₂) :
      Rewrites r (s :: u₁) (s :: u₂)

lemma Rewrites.exists_parts (hr : r.Rewrites u v) :
    ∃ p q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q := by
  induction hr with
  | head_leaf _ _ s | head_node _ _ _ s =>
    use [], s
    simp
  | cons r x rw hrs =>
    rcases hrs with ⟨p, q, rfl, rfl⟩
    use x :: p, q
    simp

lemma Rewrites.input_output : r.Rewrites [.nonterminal r.input] r.output := by
  cases r
  · simpa using head_leaf _ _ []
  · simpa using head_node _ _ _ []

lemma rewrites_of_exists_parts (r : ChomskyNormalFormRule T N) (p q : List (Symbol T N)) :
    r.Rewrites (p ++ [Symbol.nonterminal r.input] ++ q) (p ++ r.output ++ q) := by
    induction p with
    | nil => cases r <;> constructor
    | cons _ _ hr => exact Rewrites.cons r _ hr

/-- Rule `r` rewrites string `u` to string `v` iff they share both a prefix `p` and postfix `q`
such that the remaining middle part of `u` is the input of `r` and the remaining middle part
of `v` is the output of `r`. -/
theorem rewrites_iff {r : ChomskyNormalFormRule T N} (u v : List (Symbol T N)) :
    r.Rewrites u v ↔ ∃ p q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q := by
  constructor
  · apply Rewrites.exists_parts
  · rintro ⟨p, q, rfl, rfl⟩
    apply rewrites_of_exists_parts

/-- Add extra prefix to cnf rewriting. -/
lemma Rewrites.append_left {r : ChomskyNormalFormRule T N} {u v : List (Symbol T N)}
    (huv : r.Rewrites u v) (p : List (Symbol T N)) : r.Rewrites (p ++ u) (p ++ v) := by
  induction p <;> tauto

/-- Add extra postfix to cnf rewriting. -/
lemma Rewrites.append_right {r : ChomskyNormalFormRule T N} {u v : List (Symbol T N)}
    (huv : r.Rewrites u v) (p : List (Symbol T N)) : r.Rewrites (u ++ p) (v ++ p) := by
  induction huv <;> tauto

/-- Translation of `ChomskyNormalFormRule` to `ContextFreeRule` -/
def toCFGRule (r : ChomskyNormalFormRule T N) : ContextFreeRule T N :=
  match r with
  | leaf n t => ⟨n, [Symbol.terminal t]⟩
  | node nᵢ n₁ n₂ => ⟨nᵢ, [Symbol.nonterminal n₁, Symbol.nonterminal n₂]⟩

lemma Rewrites.toCFGRule_match {u v : List (Symbol T N)} {r : ChomskyNormalFormRule T N}
    (huv : r.Rewrites u v) :
    r.toCFGRule.Rewrites u v := by
  induction huv <;> tauto

lemma Rewrites.match_toCFGRule {u v : List (Symbol T N)} {r : ChomskyNormalFormRule T N}
    (huv : r.toCFGRule.Rewrites u v) :
    r.Rewrites u v := by
  induction huv with
  | head => cases r <;> tauto
  | cons s _ ih => exact Rewrites.cons r s ih

end ChomskyNormalFormRule

namespace ChomskyNormalFormGrammar

/-- Given a cnf grammar `g` and strings `u` and `v`
`g.Produces u v` means that one step of a cnf transformation by a rule from `g` sends
`u` to `v`. -/
def Produces (g : ChomskyNormalFormGrammar T) (u v : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, r.Rewrites u v

/-- Given a cnf grammar `g` and strings `u` and `v`
`g.Derives u v` means that `g` can transform `u` to `v` in some number of rewriting steps. -/
abbrev Derives (g : ChomskyNormalFormGrammar T) :
    List (Symbol T g.NT) → List (Symbol T g.NT) → Prop :=
  Relation.ReflTransGen g.Produces

/-- Given a cnf grammar `g` and a string `s`
`g.Generates s` means that `g` can transform its initial nonterminal c `s` in some number of
rewriting steps. -/
def Generates (g : ChomskyNormalFormGrammar T) (u : List (Symbol T g.NT)) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] u

/-- The language (set of words) that can be generated by a given cnf grammar `g`. -/
def language (g : ChomskyNormalFormGrammar T) : Language T :=
  { w | g.Generates (w.map Symbol.terminal) }

/-- A given word `w` belongs to the language generated by a given cnf grammar `g` iff
`g` can derive the word `w` (wrapped as a string) from the initial nonterminal of `g` in some
number of steps. -/
@[simp]
lemma mem_language_iff (g : ChomskyNormalFormGrammar T) (w : List T) :
    w ∈ g.language ↔ g.Generates (w.map Symbol.terminal) := by
  rfl

variable {g : ChomskyNormalFormGrammar T}

@[refl]
lemma Derives.refl (u : List (Symbol T g.NT)) : g.Derives u u :=
  Relation.ReflTransGen.refl

lemma Produces.single {u v : List (Symbol T g.NT)} (hvw : g.Produces u v) : g.Derives u v :=
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

/-- Add extra prefix to cnf producing. -/
lemma Produces.append_left {u v : List (Symbol T g.NT)}
    (huv : g.Produces u v) (p : List (Symbol T g.NT)) :
    g.Produces (p ++ u) (p ++ v) :=
  match huv with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_left p⟩

/-- Add extra postfix to cnf producing. -/
lemma Produces.append_right {u v : List (Symbol T g.NT)}
    (huv : g.Produces u v) (p : List (Symbol T g.NT)) :
    g.Produces (u ++ p) (v ++ p) :=
  match huv with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_right p⟩

/-- Add extra prefix to cnf deriving. -/
lemma Derives.append_left {u v : List (Symbol T g.NT)}
    (huv : g.Derives u v) (p : List (Symbol T g.NT)) :
    g.Derives (p ++ u) (p ++ v) := by
  induction huv with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_left p

/-- Add extra postfix to cnf deriving. -/
lemma Derives.append_right {u v : List (Symbol T g.NT)}
    (huv : g.Derives u v) (p : List (Symbol T g.NT)) :
    g.Derives (u ++ p) (v ++ p) := by
  induction huv with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_right p

theorem Derives.head_induction_on {v : List (Symbol T g.NT)} {P : ∀ u, g.Derives u v → Prop}
    {u : List (Symbol T g.NT)} (huv : g.Derives u v)
    (refl : P v (Derives.refl v))
    (head : ∀ {u w} (huw : g.Produces u w) (hwv : g.Derives w v), P w hwv → P u (hwv.head huw)) :
    P u huv :=
  Relation.ReflTransGen.head_induction_on huv refl head

/-! `ChomskyNormalFormGrammar` to `ContextFreeGrammar` translation and related properties -/
section toCFG

variable [DecidableEq T]

/-- Translation of `ChomskyNormalFormGrammar` to `ContextFreeGrammar` -/
noncomputable def toCFG (g : ChomskyNormalFormGrammar T) [DecidableEq g.NT] :
    ContextFreeGrammar T where
  NT := g.NT
  initial := g.initial
  rules := (g.rules.toList.map ChomskyNormalFormRule.toCFGRule).toFinset

variable {g : ChomskyNormalFormGrammar T} [DecidableEq g.NT]

lemma Produces.toCFG_match {u v : List (Symbol T g.NT)} (huv : g.Produces u v) :
    g.toCFG.Produces u v := by
  rcases huv with ⟨r, rin, hrw⟩
  use r.toCFGRule
  constructor
  · simp only [toCFG, List.mem_toFinset, List.mem_map, Finset.mem_toList]
    use r
  · exact ChomskyNormalFormRule.Rewrites.toCFGRule_match hrw

lemma Derives.toCFG_match {u v : List (Symbol T g.NT)} (huv : g.Derives u v) :
    g.toCFG.Derives u v := by
  induction huv with
  | refl => rfl
  | tail _ hp ih =>
    apply ih.trans_produces
    exact Produces.toCFG_match hp

lemma Generates.toCFG_match {u : List (Symbol T g.NT)} (hu : g.Generates u) : g.toCFG.Generates u :=
  Derives.toCFG_match hu

lemma Produces.match_toCFG {u v : List (Symbol T g.NT)} (huv : g.toCFG.Produces u v) :
    g.Produces u v := by
  rcases huv with ⟨r, hrg, huv⟩
  simp only [toCFG, List.mem_map] at hrg
  rw [List.mem_toFinset] at hrg
  obtain ⟨r', hrg', rfl⟩ := List.mem_map.1 hrg
  exact ⟨r', Finset.mem_toList.1 hrg', ChomskyNormalFormRule.Rewrites.match_toCFGRule huv⟩

lemma Derives.match_toCFG {u v : List (Symbol T g.NT)} (huv : g.toCFG.Derives u v) :
    g.Derives u v := by
  induction huv with
  | refl => rfl
  | tail _ hp ih => exact ih.trans_produces (Produces.match_toCFG hp)

lemma Generates.match_toCFG {u : List (Symbol T g.NT)} (hu : g.toCFG.Generates u) : g.Generates u :=
  Derives.match_toCFG hu

theorem toCFG_correct {u : List (Symbol T g.NT)} : g.Generates u ↔ g.toCFG.Generates u :=
  ⟨Generates.toCFG_match, Generates.match_toCFG⟩

end toCFG

/-! Alternative definition of `ChomskyNormalFormGrammar.Derives` which allows to use well-founded
induction on derivations, by explicitely counting the number of steps of the transformation -/
section derivesIn

/-- Given a context-free grammar `g`, strings `u` and `v`, and number `n`
`g.DerivesIn u v n` means that `g` can transform `u` to `v` in `n` rewriting steps. -/
inductive DerivesIn (g : ChomskyNormalFormGrammar.{uN} T) :
    List (Symbol T g.NT) → List (Symbol T g.NT) → ℕ → Prop
  /-- 0 steps entail no transformation -/
  | refl (w : List (Symbol T g.NT)) : g.DerivesIn w w 0
  /-- n + 1 steps, if transforms `u` to `v` in n steps, and `v` to `w` in 1 step  -/
  | tail (u v w : List (Symbol T g.NT)) (n : ℕ) :
    g.DerivesIn u v n → g.Produces v w → g.DerivesIn u w n.succ

lemma derives_iff_derivesIn (g : ChomskyNormalFormGrammar.{uN} T) (v w : List (Symbol T g.NT)) :
    g.Derives v w ↔ ∃ n : ℕ, g.DerivesIn v w n := by
  constructor
  · intro hgvw
    induction hgvw with
    | refl =>
      use 0
      left
    | tail _ last ih =>
      obtain ⟨n, ihn⟩ := ih
      use n.succ
      right
      · exact ihn
      · exact last
  · intro ⟨n, hgvwn⟩
    induction hgvwn with
    | refl => rfl
    | tail _ _ _ _ last ih => exact ih.trans_produces last

lemma mem_language_iff_derivesIn (g : ChomskyNormalFormGrammar.{uN} T) (w : List T) :
    w ∈ g.language ↔ ∃ n, g.DerivesIn [Symbol.nonterminal g.initial] (w.map Symbol.terminal) n := by
  rw [mem_language_iff]
  exact derives_iff_derivesIn g _ _

variable {g : ChomskyNormalFormGrammar.{uN} T}

lemma DerivesIn.zero_steps (w : List (Symbol T g.NT)) : g.DerivesIn w w 0 := by
  left

lemma DerivesIn.zero_steps_eq {u v : List (Symbol T g.NT)} (huv: g.DerivesIn u v 0) :
    u = v:= by
  cases huv
  rfl

lemma Produces.single_step {v w : List (Symbol T g.NT)} (hvw : g.Produces v w) :
    g.DerivesIn v w 1 := by
  right
  · left
  · exact hvw

variable {n : ℕ}

lemma DerivesIn.trans_produces {u v w : List (Symbol T g.NT)}
    (huv : g.DerivesIn u v n) (hvw : g.Produces v w) :
    g.DerivesIn u w n.succ :=
  DerivesIn.tail u v w n huv hvw

@[trans]
lemma DerivesIn.trans {u v w : List (Symbol T g.NT)} {m : ℕ}
    (huv : g.DerivesIn u v n) (hvw : g.DerivesIn v w m) :
    g.DerivesIn u w (n + m) := by
  induction hvw with
  | refl => exact huv
  | tail _ _ _ _ last ih => exact trans_produces ih last

lemma Produces.trans_derivesIn {u v w : List (Symbol T g.NT)}
    (huv : g.Produces u v) (hvw : g.DerivesIn v w n) :
    g.DerivesIn u w n.succ :=
  n.succ_eq_one_add ▸ huv.single_step.trans hvw

lemma DerivesIn.tail_of_succ {u w : List (Symbol T g.NT)} (huw : g.DerivesIn u w n.succ) :
    ∃ v : List (Symbol T g.NT), g.DerivesIn u v n ∧ g.Produces v w := by
  cases huw with
  | tail v w n huv hvw =>
    use v

lemma DerivesIn.head_of_succ {u w : List (Symbol T g.NT)} (huw : g.DerivesIn u w n.succ) :
    ∃ v : List (Symbol T g.NT), g.Produces u v ∧ g.DerivesIn v w n := by
  induction n generalizing w with
  | zero =>
    cases huw with
    | tail v w n huv hvw =>
      cases huv with
      | refl => exact ⟨w, hvw, zero_steps w⟩
  | succ m ih =>
    cases huw with
    | tail v w n huv hvw =>
      obtain ⟨x, hux, hxv⟩ := ih huv
      exact ⟨x, hux, hxv.trans_produces hvw⟩

/-- Add extra prefix to context-free deriving (number of steps unchanged). -/
lemma DerivesIn.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesIn v w n) (p : List (Symbol T g.NT)) :
    g.DerivesIn (p ++ v) (p ++ w) n := by
  induction hvw with
  | refl => left
  | tail _ _ _ _ last ih => exact ih.trans_produces <| last.append_left p

/-- Add extra postfix to context-free deriving (number of steps unchanged). -/
lemma DerivesIn.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.DerivesIn v w n) (p : List (Symbol T g.NT)) :
    g.DerivesIn (v ++ p) (w ++ p) n := by
  induction hvw with
  | refl => left
  | tail _ _ _ _ last ih => exact ih.trans_produces <| last.append_right p

lemma DerivesIn.append_split {p q w : List (Symbol T g.NT)} {n : ℕ}
    (hpqw : g.DerivesIn (p ++ q) w n) :
    ∃ x y m₁ m₂, w = x ++ y ∧ g.DerivesIn p x m₁ ∧ g.DerivesIn q y m₂ ∧ n = m₁ + m₂ := by
  cases n with
  | zero =>
    cases hpqw
    exact ⟨p, q, 0, 0, rfl, DerivesIn.refl p, DerivesIn.refl q, rfl⟩
  | succ n =>
    obtain ⟨v, hp, hd⟩ := hpqw.head_of_succ
    obtain ⟨r, hrg, hr⟩ := hp
    obtain ⟨p', q', heq, hv⟩ := hr.exists_parts
    rw [List.append_assoc, List.singleton_append] at heq
    have append_eq_append_cons {p q x y : List (Symbol T g.NT)} {v : Symbol T g.NT}
        (hpqxvy : p ++ q = x ++ v :: y) :
        (∃ w, y = w ++ q ∧ p = x ++ v :: w) ∨ (∃ w, x = p ++ w ∧ q = w ++ v :: y) := by
      rw [List.append_eq_append_iff] at hpqxvy
      cases hpqxvy with
      | inl hxq =>
        obtain ⟨a, _, hq⟩ := hxq
        right
        use a
      | inr hpy =>
        obtain ⟨a, rfl, hq⟩ := hpy
        cases a with
        | nil =>
          right
          use []
          rw [hq]
          constructor
          · repeat rw [List.append_nil]
          · rfl
        | cons d l =>
          left
          use l
          rw [List.cons_append, List.cons.injEq] at hq
          rw [hq.1]
          exact ⟨hq.2, rfl⟩
    rcases append_eq_append_cons heq with ⟨a, hq', hp⟩ | ⟨a, hp', hq⟩
    · rw [hv, hq', ← List.append_assoc] at hd
      obtain ⟨x, y, m₁, m₂, hw, hd₁, hd₂, hn⟩ := hd.append_split
      use x, y, (m₁ + 1), m₂
      constructor
      · exact hw
      · constructor
        · apply Produces.trans_derivesIn
          · use r
            constructor
            · exact hrg
            · rw [hp, ← List.singleton_append, ← List.append_assoc]
              apply r.rewrites_of_exists_parts
          · exact hd₁
        · exact ⟨hd₂, by omega⟩
    · rw [hv, hp', List.append_assoc, List.append_assoc] at hd
      obtain ⟨x, y, m₁, m₂, hw, hd₁, hd₂, hn⟩ := hd.append_split
      use x, y, m₁, m₂ + 1, hw, hd₁
      constructor
      · apply Produces.trans_derivesIn
        · use r, hrg
          rw [hq, ← List.singleton_append, ← List.append_assoc]
          apply r.rewrites_of_exists_parts
        · rwa [List.append_assoc]
      · omega

lemma DerivesIn.three_split {p q r w : List (Symbol T g.NT)} {n : ℕ}
    (hg : g.DerivesIn (p ++ q ++ r) w n) :
  ∃ x y z m₁ m₂ m₃, w = x ++ y ++ z ∧ g.DerivesIn p x m₁ ∧ g.DerivesIn q y m₂
    ∧ g.DerivesIn r z m₃ ∧ n = m₁ + m₂ + m₃ := by
  obtain ⟨x', z, m₁', m₃, hw₂, hd₁', hd₃, hn₂⟩ := hg.append_split
  obtain ⟨x, y, m₁, m₂, hw₁, hd₁, hd₂, hn₁⟩ := hd₁'.append_split
  exact ⟨x, y, z, m₁, m₂, m₃, hw₁ ▸ hw₂, hd₁, hd₂, hd₃, hn₁ ▸ hn₂⟩

@[elab_as_elim]
lemma DerivesIn.head_induction_on {b : List (Symbol T g.NT)}
    {P : ∀ n : ℕ, ∀ a : List (Symbol T g.NT), g.DerivesIn a b n → Prop}
    (refl : P 0 b (DerivesIn.zero_steps b))
    (head : ∀ {n a c} (hac : g.Produces a c) (hcb : g.DerivesIn c b n),
      P n c hcb → P n.succ a (hac.trans_derivesIn hcb))
    {a : List (Symbol T g.NT)} (hab : g.DerivesIn a b n) :
    P n a hab := by
  induction hab with
  | refl => exact refl
  | tail _ _ _ _ last ih =>
    apply ih
    · exact head last _ refl
    · intro _ _ _ produc deriv
      exact head produc (deriv.tail _ _ _ _ last)

end derivesIn

end ChomskyNormalFormGrammar
