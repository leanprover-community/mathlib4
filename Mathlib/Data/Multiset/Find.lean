/-
Copyright (c) 2026 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module
public import Mathlib.Data.List.Find
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Set.Subsingleton

/-!
# Finding subsingleton elements within multisets

This module provides `Multiset.find? s p ⋯`, which lifts `List.find?` to multisets.
-/

public section

namespace Multiset
variable {α : Type*} (p : α → Prop) [DecidablePred p]

/-- `s.find? p ⋯` finds the subsingleton element of `s` satisfying the condition `p`, if one exists.

This is the multiset version of `List.find?`,
and is like `Multiset.choose`, but `Option`-valued. -/
@[expose] def find? (s : Multiset α) : {x ∈ s | p x}.Subsingleton → Option α :=
  Quotient.recOn s (fun l _ => l.find? p) fun l₁ l₂ h => by
    unfold Eq.ndrec
    rw [eqRec_eq_cast, cast_eq_iff_heq]
    refine Function.hfunext ?_ (fun hp₁ hp₂ _ ↦ heq_of_eq ?_)
    · congr!
      exact Quotient.sound h
    refine List.find?_eq_find?_of_perm h ?_
    simpa using hp₁

@[simp, grind =]
theorem find?_coe (l : List α) (hp) :
    (l : Multiset α).find? p hp = l.find? (fun a => p a) := rfl

theorem find?_some {a : α} {s : Multiset α} {hp} :
    s.find? p hp = some a → p a := by
  induction s using Quotient.inductionOn with | _ l
  simp only [quot_mk_to_coe, find?_coe _ _ hp]
  simpa using l.find?_some  (p := (p ·))

@[simp]
theorem find?_zero : (0 : Multiset α).find? p (by simp) = none := rfl

@[simp]
theorem find?_cons (a : α) (s : Multiset α) (hp) :
    (cons a s).find? p hp = if h : p a then some a else s.find? p (by grind) := by
  induction s using Quotient.inductionOn
  simp only [quot_mk_to_coe, cons_coe]
  grind

@[simp]
theorem find?_singleton (a : α) (hp) :
    ({a} : Multiset α).find? p hp = if p a then some a else none :=
  find?_cons _ _ _ _

@[simp]
theorem find?_add (s t : Multiset α) (hp) :
    (s + t).find? p hp =
      (s.find? p (hp.anti <| by grind)).or (t.find? p (hp.anti <| by grind)) := by
  induction s, t using Quotient.inductionOn₂
  exact List.find?_append

variable {p} in
@[simp, grind =]
theorem find?_eq_some_iff {a : α} {s : Multiset α} (hp) :
    s.find? p hp = some a ↔ a ∈ s ∧ p a := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [find?_cons]
    split
    · dsimp [Set.Subsingleton] at hp
      specialize hp ⟨mem_cons_self _ _, ‹p x›⟩
      grind
    · simp_rw [ih]
      grind

variable {p} in
@[simp, grind =]
theorem find?_eq_none_iff {s : Multiset α} (hp) :
    s.find? p hp = none ↔ ∀ a ∈ s, ¬ p a := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [find?_cons]
    dsimp [Set.Subsingleton] at hp
    grind

/-- If two predicates agree on all the elements, so does `find?`. -/
@[congr]
theorem find?_congr {p₁ p₂ : α → Prop} [DecidablePred p₁] [DecidablePred p₂] {s : Multiset α}
    (hp₁ : {x ∈ s | p₁ x}.Subsingleton) (h : ∀ x ∈ s, p₁ x ↔ p₂ x) :
    s.find? p₁ hp₁ = s.find? p₂
      (by simp_rw +contextual [← exists_prop, ← h, exists_prop, hp₁]) := by
  induction s using Quotient.ind with simp +contextual [h]

theorem find?_eq_choose {s : Multiset α} (hp : ∃! x, x ∈ s ∧ p x) :
    s.find? p hp.setSubsingleton = some (s.choose p hp) := by
  ext a
  refine find?_eq_some_iff _ |>.trans ?_
  simp only [Option.some.injEq, choose_eq_iff]

end Multiset
