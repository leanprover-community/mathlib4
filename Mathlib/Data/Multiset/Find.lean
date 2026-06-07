/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Set.Subsingleton

/-!
# Finding subsingleton elements within multisets

This module provides `Multiset.findX? s p ⋯`.
-/

@[expose] public section

/-- A version of `List.find?` that returns a proof. -/
abbrev _root_.List.findX? {α : Type*} (p : α → Prop) [DecidablePred p] (l : List α) :
    Option {x // p x} :=
  l.findSome? (fun x => if h : p x then some ⟨x, h⟩ else none)

namespace Multiset
variable {α : Type*} (p : α → Prop) [DecidablePred p] (hp : {x | p x}.Subsingleton)


/-- `s.findX? p ⋯` finds the subsingleton element of `s` satisfing the condition `p`, if one exists.

This is like `Multiset.chooseX`, but `Option`-valued. -/
def findX? (s : Multiset α) : Option {a : α // p a} :=
  Quotient.recOn s (List.findX? p) fun l₁ l₂ h => by
    induction h with
    | nil => rfl
    | cons x _ ih =>
      grind
    | swap x y l =>
      dsimp [Set.Subsingleton] at hp
      by_cases p x <;> by_cases p y <;> grind
    | trans _ _ ih1 ih2 =>
      simp only [quot_mk_to_coe, eq_rec_constant] at *
      exact ih1.trans ih2

@[simp, grind =]
theorem findX?_coe (l : List α) :
    (l : Multiset α).findX? p hp = l.findX? (fun a => p a) := rfl

@[simp]
theorem find?_zero : (0 : Multiset α).findX? p hp = none := rfl

@[simp]
theorem findX?_cons (a : α) (s : Multiset α) :
    (cons a s).findX? p hp = if h : p a then some ⟨a, h⟩ else s.findX? p hp := by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, cons_coe]
  grind

@[simp]
theorem findX?_singleton (a : α) :
    ({a} : Multiset α).findX? p hp = if h : p a then some ⟨a, h⟩ else none :=
  findX?_cons _ _ _ _

@[simp]
theorem findX?_add (s t : Multiset α) :
    (s + t).findX? p hp = (s.findX? p hp <|> t.findX? p hp) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [cons_add, findX?_cons, ih, findX?_cons]
    split_ifs <;> simp

@[simp]
theorem mem_findX?_iff {a : {a : α // p a}} {s : Multiset α} :
    a ∈ s.findX? p hp ↔ a.1 ∈ s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [findX?_cons]
    dsimp [Set.Subsingleton] at hp
    grind


-- theorem findX?_eq_choose {s : Multiset α} (hp : ∃! x, x ∈ s ∧ p x):
--     s.findX? p (by grind) = some ⟨s.choose p hp, s.choose_property p hp⟩ := by
--   ext
--   refine mem_findX?_iff _ _ |>.trans ?_
--   simp [Subtype.ext_iff, choose_eq]

end Multiset
