/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Data.List.Infix
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Basic

/-!
# List lemmas for Perron–Frobenius

Auxiliary lemmas on `List` used by quiver paths and matrix Perron–Frobenius theory.

## Main results

* `ContainsDup` and `nodup_iff_not_contains_dup`: duplicate detection via counting.
* `exists_pos_get_of_dropLast_count_ge_two`: locate a repeated vertex in a list prefix.

## Tags

list, quiver path, Perron–Frobenius theorem
-/

@[expose] public section

namespace List
variable {α : Type*}

/-- Any `x ∈ l` gives a decomposition `l = l₁ ++ x :: l₂`. -/
lemma exists_mem_split {l : List α} {x : α} (h : x ∈ l) :
    ∃ l₁ l₂, l = l₁ ++ x :: l₂ := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    rcases mem_cons.mp h with rfl | h'
    · exact ⟨[], ys, rfl⟩
    · obtain ⟨l₁, l₂, rfl⟩ := ih h'
      exact ⟨y :: l₁, l₂, rfl⟩

lemma get_eq_get_dropLast {l : List α} {i : Nat} (hi : i < l.length - 1) :
    l.get ⟨i, Nat.lt_of_lt_pred hi⟩ =
      l.dropLast.get ⟨i, by rw [length_dropLast]; omega⟩ := by
  simp [get_eq_getElem, dropLast_eq_take, getElem_take]

variable [DecidableEq α]

/-- A list contains a duplicate element if the count of some element is greater than 1. -/
def ContainsDup (l : List α) : Prop := ∃ x, 2 ≤ l.count x

lemma nodup_iff_not_contains_dup {l : List α} : l.Nodup ↔ ¬l.ContainsDup := by
  simp only [ContainsDup, nodup_iff_count_le_one, not_exists, not_le]
  grind

lemma idxOf_eq_idxOf_of_isPrefix {v : α} {l₁ l₂ : List α}
    (hpref : l₁ <+: l₂) (hv : v ∈ l₁) : idxOf v l₂ = idxOf v l₁ :=
  (IsPrefix.idxOf_eq_of_mem hpref hv).symm

lemma mem_tail_of_count_ge_two {x : α} {l : List α} (h : 2 ≤ l.count x) : x ∈ l.tail := by
  cases l with
  | nil => simp at h
  | cons hd tl =>
    have hpos : 0 < tl.count x := by
      by_contra h0
      push Not at h0
      by_cases hhd : hd = x <;> simp [hhd, Nat.eq_zero_of_le_zero h0] at h
    exact count_pos_iff.mp hpos

lemma get_idxOf_of_mem {l : List α} {x : α} (h : x ∈ l) :
    l.get ⟨idxOf x l, idxOf_lt_length_of_mem h⟩ = x := by
  rw [get_eq_getElem, getElem_idxOf (idxOf_lt_length_of_mem h)]

lemma exists_pos_get_of_dropLast_count_ge_two {l : List α} {x : α}
    (h : 2 ≤ l.dropLast.count x) :
    ∃ (i : Nat) (hi : i < l.length), 0 < i ∧ i < l.length - 1 ∧ l.get ⟨i, hi⟩ = x := by
  have hx_tail := mem_tail_of_count_ge_two h
  have hlen : 2 ≤ l.length := by
    have := Nat.le_trans h count_le_length
    rw [length_dropLast] at this
    omega
  match l with
  | [] | [_] => simp at hlen
  | y :: z :: tl =>
    have hx_mem : x ∈ (z :: tl).dropLast := by
      simpa [dropLast_cons_cons, tail_cons] using hx_tail
    let i := (z :: tl).dropLast.idxOf x + 1
    have hidx := idxOf_lt_length_of_mem hx_mem
    have hdl : (z :: tl).dropLast.length = tl.length := by
      simp only [length_cons, length_dropLast]; omega
    have hi_pred : i < (y :: z :: tl).length - 1 := by
      dsimp [i, length_cons]; rw [hdl] at hidx; exact Nat.succ_lt_succ hidx
    have hi_lt_len : i < (y :: z :: tl).length := Nat.lt_of_lt_pred hi_pred
    have hi_z : (z :: tl).dropLast.idxOf x < (z :: tl).length - 1 := by
      rw [show (z :: tl).length - 1 = (z :: tl).dropLast.length from by
        rw [length_dropLast, length_cons]]
      exact hidx
    refine ⟨i, hi_lt_len, Nat.succ_pos _, hi_pred, ?_⟩
    simp only [i]
    rw [get_cons_succ, get_eq_get_dropLast hi_z, get_idxOf_of_mem hx_mem]

end List
