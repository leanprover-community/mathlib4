/-
Copyright (c) 2024 Bolton Bailey. All rights reserved.
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

-- # rget

/-- Get element `t` of `l` from the right.
For example `[0,1].rget 0 = 1`.-/
def rget (l : List α) (t : Fin l.length) :=
  l.get ⟨l.length - (t+1),
    (Nat.sub_lt_self (Nat.zero_lt_succ ↑t) (by rw [Nat.succ_le] ; exact t.isLt))⟩

@[simp]
theorem rget_cons_eq_self {l : List α} {x : α} {t : Fin l.length} :
    (x :: l).rget ⟨t.val, (lt_trans t.isLt (Nat.lt_succ_self _))⟩ = l.rget t := by
  unfold rget
  have : t + 1 ≤ l.length := by rw [Nat.succ_le] ; exact t.isLt
  simp_rw [length_cons, Nat.succ_sub this]
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
  unfold rget ; apply getElem_singleton


-- # rdrop


-- # rtake

lemma rget_cons_rtake {l : List α} {t : Fin l.length} :
    l.rtake (t+1) = (l.rget t) :: (l.rtake t) := by
  unfold rtake rget
  cases' l with x l
  · have := t.isLt
    contradiction
  · have : t ≤ l.length := by rw [← Nat.lt_succ] ; apply t.isLt
    simp_rw [List.length_cons, Nat.succ_sub_succ, Nat.succ_sub this]
    apply drop_eq_getElem_cons


end List
