/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yves Jäckle
-/
import Mathlib.Data.List.DropRight

/-! # rget

This file defines `rget` and provides theorems for working with it. `rget` is used to
access an element of a list by numerical index, starting from the right hand side of the list.
-/

variable {α : Sort _}

namespace List

/-! ### rget -/

/-- Get element `t` of `l` from the right.
For example `[0,1].rget 0 = 1`.-/
def rget (l : List α) (t : Fin l.length) :=
  l.get t.rev

@[simp]
theorem rget_cons_eq_self {l : List α} {x : α} {t : Fin l.length} :
    (x :: l).rget (t.castLE (Nat.le_succ _)) = l.rget t := by
  unfold rget
  have : t + 1 ≤ l.length := by rw [Nat.succ_le]; exact t.isLt
  dsimp
  simp_rw [Nat.succ_sub this]
  rfl

@[simp]
theorem rget_cons_length {l : List α} {x : α} :
    (x :: l).rget ⟨l.length, (Nat.le.refl)⟩ = x := by
  unfold rget
  dsimp
  simp_rw [Nat.sub_self]
  apply get_cons_zero


@[simp]
lemma rget_singleton {x : α} {n : Fin 1} : [x].rget n = x := by
  unfold rget; apply getElem_singleton


lemma rget_append_right {α : Type _} {l L : List α} (n : Fin l.length) :
    (L ++ l).rget (n.castLE (by rw [length_append]; apply Nat.le_add_left)) = l.rget n := by
  induction' L with x xs ih
  · rfl
  · simp_rw [cons_append, ← ih]
    convert rget_cons_eq_self using 2
    rfl

lemma rget_suffix {α : Type _} {l L : List α} (m : l <:+ L) (n : Fin l.length) :
    L.rget (n.castLE (IsSuffix.length_le m)) = l.rget n := by
  rw [suffix_iff_eq_append] at m
  have := @rget_append_right _ l (L.take (L.length - l.length)) n
  convert this
  exact m.symm

/-! ### rtake -/

lemma rget_cons_rtake {l : List α} {t : Fin l.length} :
    l.rtake (t+1) = (l.rget t) :: (l.rtake t) := by
  unfold rtake rget
  cases' l with x l
  · have := t.isLt
    contradiction
  · have : t ≤ l.length := by rw [← Nat.lt_succ]; apply t.isLt
    dsimp
    simp_rw [Nat.succ_sub_succ, Nat.succ_sub this]
    apply drop_eq_getElem_cons


end List
