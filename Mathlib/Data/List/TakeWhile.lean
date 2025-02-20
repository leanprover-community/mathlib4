/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Set

/-! ### List.takeWhile and List.dropWhile -/

namespace List

variable {α : Type*} (p : α → Bool)

theorem dropWhile_get_zero_not (l : List α) (hl : 0 < (l.dropWhile p).length) :
    ¬p ((l.dropWhile p).get ⟨0, hl⟩) := by
  induction' l with hd tl IH
  · cases hl
  · simp only [dropWhile]
    by_cases hp : p hd
    · simp_all only [get_eq_getElem]
      apply IH
      simp_all only [dropWhile_cons_of_pos]
    · simp [hp]

@[deprecated (since := "2024-08-19")] alias dropWhile_nthLe_zero_not := dropWhile_get_zero_not

variable {p} {l : List α}

@[simp]
theorem dropWhile_eq_nil_iff : dropWhile p l = [] ↔ ∀ x ∈ l, p x := by
  induction' l with x xs IH
  · simp [dropWhile]
  · by_cases hp : p x <;> simp [hp, IH]

@[simp]
theorem takeWhile_eq_self_iff : takeWhile p l = l ↔ ∀ x ∈ l, p x := by
  induction' l with x xs IH
  · simp
  · by_cases hp : p x <;> simp [hp, IH]

@[simp]
theorem takeWhile_eq_nil_iff : takeWhile p l = [] ↔ ∀ hl : 0 < l.length, ¬p (l.get ⟨0, hl⟩) := by
  induction' l with x xs IH
  · simp only [takeWhile_nil, Bool.not_eq_true, true_iff]
    intro h
    simp at h
  · by_cases hp : p x <;> simp [hp, IH]

theorem mem_takeWhile_imp {x : α} (hx : x ∈ takeWhile p l) : p x := by
  induction l with simp [takeWhile] at hx
  | cons hd tl IH =>
    cases hp : p hd
    · simp [hp] at hx
    · rw [hp, mem_cons] at hx
      rcases hx with (rfl | hx)
      · exact hp
      · exact IH hx

theorem takeWhile_takeWhile (p q : α → Bool) (l : List α) :
    takeWhile p (takeWhile q l) = takeWhile (fun a => p a ∧ q a) l := by
  induction' l with hd tl IH
  · simp
  · by_cases hp : p hd <;> by_cases hq : q hd <;> simp [takeWhile, hp, hq, IH]

theorem takeWhile_idem : takeWhile p (takeWhile p l) = takeWhile p l := by
  simp_rw [takeWhile_takeWhile, and_self_iff, Bool.decide_coe]

variable (p) (l)

lemma find?_eq_head?_dropWhile_not :
    l.find? p = (l.dropWhile (fun x ↦ ! (p x))).head? := by
  induction l
  case nil => simp
  case cons head tail hi =>
    set ph := p head with phh
    rcases ph with rfl | rfl
    · have phh' : ¬(p head = true) := by simp [phh.symm]
      rw [find?_cons_of_neg _ phh', dropWhile_cons_of_pos]
      · exact hi
      · simpa using phh
    · rw [find?_cons_of_pos _ phh.symm, dropWhile_cons_of_neg]
      · simp
      · simpa using phh

lemma find?_not_eq_head?_dropWhile :
    l.find? (fun x ↦ ! (p x)) = (l.dropWhile p).head? := by
  convert l.find?_eq_head?_dropWhile_not ?_
  simp

variable {p} {l}

lemma find?_eq_head_dropWhile_not (h : ∃ x ∈ l, p x) :
    l.find? p = some ((l.dropWhile (fun x ↦ ! (p x))).head (by simpa using h)) := by
  rw [l.find?_eq_head?_dropWhile_not p, ← head_eq_iff_head?_eq_some]

lemma find?_not_eq_head_dropWhile (h : ∃ x ∈ l, ¬p x) :
    l.find? (fun x ↦ ! (p x)) = some ((l.dropWhile p).head (by simpa using h)) := by
  convert l.find?_eq_head_dropWhile_not ?_
  · simp
  · simpa using h

end List
