/-
Copyright (c) 2023 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
import Mathlib.Computability.Language

/-!
# Context-Free Grammars

This file contains the definition of a context-free grammar, which is a grammar that has a single
nonterminal symbol on the left-hand side of each rule.

We restrict nonterminals of a context-free grammar to `Type` because universe polymorphism would be
cumbersome and unnecessary; we can always restrict a context-free grammar to the finitely many
nonterminal symbols that are referred to by its finitely many rules.

## Main definitions
* `ContextFreeGrammar`: A context-free grammar.
* `ContextFreeGrammar.language`: A language generated by a given context-free grammar.

## Main theorems
* `Language.IsContextFree.reverse`: The class of context-free languages is closed under reversal.
-/

open Function

/-- Rule that rewrites a single nonterminal to any string (a list of symbols). -/
@[ext]
structure ContextFreeRule (T N : Type*) where
  /-- Input nonterminal a.k.a. left-hand side. -/
  input : N
  /-- Output string a.k.a. right-hand side. -/
  output : List (Symbol T N)
deriving DecidableEq, Repr

/-- Context-free grammar that generates words over the alphabet `T` (a type of terminals). -/
structure ContextFreeGrammar (T : Type*) where
  /-- Type of nonterminals. -/
  NT : Type
  /-- Initial nonterminal. -/
  initial : NT
  /-- Rewrite rules. -/
  rules : Finset (ContextFreeRule T NT)

variable {T : Type*}

namespace ContextFreeRule
variable {N : Type*} {r : ContextFreeRule T N} {u v : List (Symbol T N)}

/-- Inductive definition of a single application of a given context-free rule `r` to a string `u`;
`r.Rewrites u v` means that the `r` sends `u` to `v` (there may be multiple such strings `v`). -/
inductive Rewrites (r : ContextFreeRule T N) : List (Symbol T N) → List (Symbol T N) → Prop
  /-- The replacement is at the start of the remaining string. -/
  | head (s : List (Symbol T N)) :
      r.Rewrites (Symbol.nonterminal r.input :: s) (r.output ++ s)
  /-- There is a replacement later in the string. -/
  | cons (x : Symbol T N) {s₁ s₂ : List (Symbol T N)} (hrs : Rewrites r s₁ s₂) :
      r.Rewrites (x :: s₁) (x :: s₂)

lemma Rewrites.exists_parts (hr : r.Rewrites u v) :
    ∃ p q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q := by
  induction hr with
  | head s =>
    use [], s
    simp
  | cons x _ ih =>
    rcases ih with ⟨p', q', rfl, rfl⟩
    use x :: p', q'
    simp

lemma Rewrites.input_output : r.Rewrites [.nonterminal r.input] r.output := by
  simpa using head []

lemma rewrites_of_exists_parts (r : ContextFreeRule T N) (p q : List (Symbol T N)) :
    r.Rewrites (p ++ [Symbol.nonterminal r.input] ++ q) (p ++ r.output ++ q) := by
  induction p with
  | nil         => exact Rewrites.head q
  | cons d l ih => exact Rewrites.cons d ih

/-- Rule `r` rewrites string `u` is to string `v` iff they share both a prefix `p` and postfix `q`
such that the remaining middle part of `u` is the input of `r` and the remaining middle part
of `u` is the output of `r`. -/
theorem rewrites_iff :
    r.Rewrites u v ↔ ∃ p q : List (Symbol T N),
      u = p ++ [Symbol.nonterminal r.input] ++ q ∧ v = p ++ r.output ++ q :=
  ⟨Rewrites.exists_parts, by rintro ⟨p, q, rfl, rfl⟩; apply rewrites_of_exists_parts⟩

lemma Rewrites.nonterminal_input_mem : r.Rewrites u v → .nonterminal r.input ∈ u := by
  simp +contextual [rewrites_iff, List.append_assoc]

/-- Add extra prefix to context-free rewriting. -/
lemma Rewrites.append_left (hvw : r.Rewrites u v) (p : List (Symbol T N)) :
    r.Rewrites (p ++ u) (p ++ v) := by
  rw [rewrites_iff] at *
  rcases hvw with ⟨x, y, hxy⟩
  use p ++ x, y
  simp_all

/-- Add extra postfix to context-free rewriting. -/
lemma Rewrites.append_right (hvw : r.Rewrites u v) (p : List (Symbol T N)) :
    r.Rewrites (u ++ p) (v ++ p) := by
  rw [rewrites_iff] at *
  rcases hvw with ⟨x, y, hxy⟩
  use x, y ++ p
  simp_all

end ContextFreeRule

namespace ContextFreeGrammar

/-- Given a context-free grammar `g` and strings `u` and `v`
`g.Produces u v` means that one step of a context-free transformation by a rule from `g` sends
`u` to `v`. -/
def Produces (g : ContextFreeGrammar T) (u v : List (Symbol T g.NT)) : Prop :=
  ∃ r ∈ g.rules, r.Rewrites u v

/-- Given a context-free grammar `g` and strings `u` and `v`
`g.Derives u v` means that `g` can transform `u` to `v` in some number of rewriting steps. -/
abbrev Derives (g : ContextFreeGrammar T) :
    List (Symbol T g.NT) → List (Symbol T g.NT) → Prop :=
  Relation.ReflTransGen g.Produces

/-- Given a context-free grammar `g` and a string `s`
`g.Generates s` means that `g` can transform its initial nonterminal to `s` in some number of
rewriting steps. -/
def Generates (g : ContextFreeGrammar T) (s : List (Symbol T g.NT)) : Prop :=
  g.Derives [Symbol.nonterminal g.initial] s

/-- The language (set of words) that can be generated by a given context-free grammar `g`. -/
def language (g : ContextFreeGrammar T) : Language T :=
  { w : List T | g.Generates (w.map Symbol.terminal) }

/-- A given word `w` belongs to the language generated by a given context-free grammar `g` iff
`g` can derive the word `w` (wrapped as a string) from the initial nonterminal of `g` in some
number of steps. -/
@[simp]
lemma mem_language_iff (g : ContextFreeGrammar T) (w : List T) :
    w ∈ g.language ↔ g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) := by
  rfl

variable {g : ContextFreeGrammar T}

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

lemma derives_iff_eq_or_head {u w : List (Symbol T g.NT)} :
    g.Derives u w ↔ u = w ∨ ∃ v : List (Symbol T g.NT), g.Produces u v ∧ g.Derives v w :=
  Relation.ReflTransGen.cases_head_iff

lemma Derives.eq_or_tail {u w : List (Symbol T g.NT)} (huw : g.Derives u w) :
    w = u ∨ ∃ v : List (Symbol T g.NT), g.Derives u v ∧ g.Produces v w :=
  Relation.ReflTransGen.cases_tail huw

lemma derives_iff_eq_or_tail {u w : List (Symbol T g.NT)} :
    g.Derives u w ↔ w = u ∨ ∃ v : List (Symbol T g.NT), g.Derives u v ∧ g.Produces v w :=
  Relation.ReflTransGen.cases_tail_iff g.Produces u w

/-- Add extra prefix to context-free producing. -/
lemma Produces.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.Produces v w) (p : List (Symbol T g.NT)) :
    g.Produces (p ++ v) (p ++ w) :=
  match hvw with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_left p⟩

/-- Add extra postfix to context-free producing. -/
lemma Produces.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.Produces v w) (p : List (Symbol T g.NT)) :
    g.Produces (v ++ p) (w ++ p) :=
  match hvw with | ⟨r, hrmem, hrvw⟩ => ⟨r, hrmem, hrvw.append_right p⟩

/-- Add extra prefix to context-free deriving. -/
lemma Derives.append_left {v w : List (Symbol T g.NT)}
    (hvw : g.Derives v w) (p : List (Symbol T g.NT)) :
    g.Derives (p ++ v) (p ++ w) := by
  induction hvw with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_left p

/-- Add extra postfix to context-free deriving. -/
lemma Derives.append_right {v w : List (Symbol T g.NT)}
    (hvw : g.Derives v w) (p : List (Symbol T g.NT)) :
    g.Derives (v ++ p) (w ++ p) := by
  induction hvw with
  | refl => rfl
  | tail _ last ih => exact ih.trans_produces <| last.append_right p

lemma Produces.exists_nonterminal_input_mem {u v : List (Symbol T g.NT)} (hguv : g.Produces u v) :
    ∃ r ∈ g.rules, .nonterminal r.input ∈ u := by
  obtain ⟨w, l, r⟩ := hguv
  exact ⟨w, l, r.nonterminal_input_mem⟩

lemma derives_nonterminal {t : g.NT} (hgt : ∀ r ∈ g.rules, r.input ≠ t) :
    ∀ s ≠ [.nonterminal t], ¬g.Derives [.nonterminal t] s := fun _ hs ↦ by
  rw [derives_iff_eq_or_head]
  push_neg
  refine ⟨hs.symm, fun _ hx ↦ ?_⟩
  have hxr := hx.exists_nonterminal_input_mem
  simp_rw [List.mem_singleton, Symbol.nonterminal.injEq] at hxr
  tauto

lemma language_eq_zero_of_forall_input_ne_initial (hg : ∀ r ∈ g.rules, r.input ≠ g.initial) :
    g.language = 0 := by ext; simp +contextual [derives_nonterminal, hg]

end ContextFreeGrammar

/-- Context-free languages are defined by context-free grammars. -/
def Language.IsContextFree (L : Language T) : Prop :=
  ∃ g : ContextFreeGrammar T, g.language = L

section closure_reversal

namespace ContextFreeRule
variable {N : Type*} {r : ContextFreeRule T N} {u v : List (Symbol T N)}

/-- Rules for a grammar for a reversed language. -/
def reverse (r : ContextFreeRule T N) : ContextFreeRule T N := ⟨r.input, r.output.reverse⟩

@[simp] lemma reverse_reverse (r : ContextFreeRule T N) : r.reverse.reverse = r := by simp [reverse]

@[simp] lemma reverse_comp_reverse :
    reverse ∘ reverse = (id : ContextFreeRule T N → ContextFreeRule T N) := by ext : 1; simp

lemma reverse_involutive : Involutive (reverse : ContextFreeRule T N → ContextFreeRule T N) :=
  reverse_reverse

lemma reverse_bijective : Bijective (reverse : ContextFreeRule T N → ContextFreeRule T N) :=
  reverse_involutive.bijective

lemma reverse_injective : Injective (reverse : ContextFreeRule T N → ContextFreeRule T N) :=
  reverse_bijective.injective

lemma reverse_surjective : Surjective (reverse : ContextFreeRule T N → ContextFreeRule T N) :=
  reverse_bijective.surjective

protected lemma Rewrites.reverse : ∀ {u v}, r.Rewrites u v → r.reverse.Rewrites u.reverse v.reverse
  | _, _, head s => by simpa using .append_left .input_output _
  | _, _, @cons _ _ _ x u v h => by simpa using h.reverse.append_right _

lemma rewrites_reverse : r.reverse.Rewrites u.reverse v.reverse ↔ r.Rewrites u v :=
  ⟨fun h ↦ by simpa using h.reverse, .reverse⟩

@[simp] lemma rewrites_reverse_comm : r.reverse.Rewrites u v ↔ r.Rewrites u.reverse v.reverse := by
  rw [← rewrites_reverse, reverse_reverse]

end ContextFreeRule

namespace ContextFreeGrammar
variable {g : ContextFreeGrammar T} {u v : List (Symbol T g.NT)} {w : List T}

/-- Grammar for a reversed language. -/
@[simps] def reverse (g : ContextFreeGrammar T) : ContextFreeGrammar T :=
  ⟨g.NT, g.initial, g.rules.map (⟨ContextFreeRule.reverse, ContextFreeRule.reverse_injective⟩)⟩

@[simp] lemma reverse_reverse (g : ContextFreeGrammar T) : g.reverse.reverse = g := by
  simp [reverse, Finset.map_map]

lemma reverse_involutive : Involutive (reverse : ContextFreeGrammar T → ContextFreeGrammar T) :=
  reverse_reverse

lemma reverse_bijective : Bijective (reverse : ContextFreeGrammar T → ContextFreeGrammar T) :=
  reverse_involutive.bijective

lemma reverse_injective : Injective (reverse : ContextFreeGrammar T → ContextFreeGrammar T) :=
  reverse_bijective.injective

lemma reverse_surjective : Surjective (reverse : ContextFreeGrammar T → ContextFreeGrammar T) :=
  reverse_bijective.surjective

lemma produces_reverse : g.reverse.Produces u.reverse v.reverse ↔ g.Produces u v :=
  (Equiv.ofBijective _ ContextFreeRule.reverse_bijective).exists_congr
    (by simp [ContextFreeRule.reverse_involutive.eq_iff])

alias ⟨_, Produces.reverse⟩ := produces_reverse

@[simp] lemma produces_reverse_comm : g.reverse.Produces u v ↔ g.Produces u.reverse v.reverse :=
  (Equiv.ofBijective _ ContextFreeRule.reverse_bijective).exists_congr
    (by simp [ContextFreeRule.reverse_involutive.eq_iff])

protected lemma Derives.reverse (hg : g.Derives u v) : g.reverse.Derives u.reverse v.reverse := by
  induction hg with
  | refl => rfl
  | tail _ orig ih => exact ih.trans_produces orig.reverse

lemma derives_reverse : g.reverse.Derives u.reverse v.reverse ↔ g.Derives u v :=
  ⟨fun h ↦ by convert h.reverse <;> simp, .reverse⟩

@[simp] lemma derives_reverse_comm : g.reverse.Derives u v ↔ g.Derives u.reverse v.reverse := by
  rw [iff_comm, ← derives_reverse, List.reverse_reverse, List.reverse_reverse]

lemma generates_reverse : g.reverse.Generates u.reverse ↔ g.Generates u := by simp [Generates]

alias ⟨_, Generates.reverse⟩ := generates_reverse

@[simp] lemma generates_reverse_comm : g.reverse.Generates u ↔ g.Generates u.reverse := by
  simp [Generates]

@[simp] lemma language_reverse : g.reverse.language = g.language.reverse := by ext; simp

end ContextFreeGrammar

/-- The class of context-free languages is closed under reversal. -/
theorem Language.IsContextFree.reverse (L : Language T) :
    L.IsContextFree → L.reverse.IsContextFree := by rintro ⟨g, rfl⟩; exact ⟨g.reverse, by simp⟩

end closure_reversal
