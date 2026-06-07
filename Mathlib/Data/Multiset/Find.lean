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

This module provides `Multiset.find? s p ⋯`
-/

@[expose] public section

namespace List

/-- If there is at most one element satifsying `p`, then `find?` agrees on permuted lists. -/
theorem find?_eq_find?_of_perm
    {α} {p : α → Bool} {l₁ l₂ : List α} (h : l₁.Perm l₂) (hp : {x | p x}.Subsingleton) :
    l₁.find? p = l₂.find? p := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    grind
  | swap x y l =>
    dsimp [Set.Subsingleton] at hp
    by_cases p x <;> by_cases p y <;> grind
  | trans _ _ ih1 ih2 =>
    exact ih1.trans ih2

end List

namespace Multiset
variable {α : Type*} (p : α → Prop) [DecidablePred p] (hp : {x | p x}.Subsingleton)


/-- `s.find? p ⋯` finds the subsingleton element of `s` satisfing the condition `p`, if one exists.

This is the multiset version of `List.find?`,
and is like `Multiset.choose`, but `Option`-valued. -/
def find? (s : Multiset α) : Option α :=
  Quotient.recOn s (List.find? p) fun l₁ l₂ h => by
    convert List.find?_eq_find?_of_perm h ?_
    · grind
    · simpa using hp

@[simp, grind =]
theorem find?_coe (l : List α) :
    (l : Multiset α).find? p hp = l.find? (fun a => p a) := rfl

theorem find?_some {a : α} {s : Multiset α} :
    s.find? p hp = some a → p a := by
  induction s using Quotient.inductionOn with | _ l
  simp only [quot_mk_to_coe, find?_coe _ hp]
  simpa using l.find?_some  (p := (p ·))

@[simp]
theorem find?_zero : (0 : Multiset α).find? p hp = none := rfl

@[simp]
theorem find?_cons (a : α) (s : Multiset α) :
    (cons a s).find? p hp = if p a then some a else s.find? p hp := by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, cons_coe]
  grind

@[simp]
theorem find?_singleton (a : α) :
    ({a} : Multiset α).find? p hp = if p a then some a else none :=
  find?_cons _ _ _ _

@[simp]
theorem find?_add (s t : Multiset α) :
    (s + t).find? p hp = (s.find? p hp).or (t.find? p hp) := by
  induction s, t using Quotient.inductionOn₂
  exact List.find?_append

@[simp, grind =]
theorem find?_eq_some_iff {a : α} {s : Multiset α} :
    s.find? p hp = some a ↔ a ∈ s ∧ p a := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [find?_cons]
    dsimp [Set.Subsingleton] at hp
    grind

/-- Note that we cannot derive `hp` from `hp'` or vice versa, as the former allos no such `x`,
while the latter only requires uniqueness within the set. -/
theorem find?_eq_choose {s : Multiset α} (hp' : ∃! x, x ∈ s ∧ p x) :
    s.find? p hp = some (s.choose p hp') := by
  ext a
  refine find?_eq_some_iff _ _ |>.trans ?_
  simp only [Option.some.injEq, choose_eq_iff]

end Multiset
