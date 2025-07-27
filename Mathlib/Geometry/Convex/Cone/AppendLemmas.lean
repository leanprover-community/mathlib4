/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Appending finite sequences

We give simple lemmas regarding multiplying, appending,
and de-appending finite sequences.

## Main results

- A basic API for appending and de-appending finite sequences

sample lemmas:
-'append_apply_lt': extracting the initial part of the append of two sequences
-'append_apply_ge': extracting the terminal part of the append of two sequences
-'append_forall_iff': appended sequences preserve predicates of its components

## Notation

 - no special notation defined

## Implementation notes

In this file finite sequences are represented by
  'v : Fin n → E' (representing vectors or module elements) and
  'c : Fin m → R' (representing scalar coefficients).

## References

 - This way of defining finite sequences is used in
  Mathlib.Data.Fin.Tuple.Basic

-/

variable {α : Type*}
variable {m n : ℕ}

namespace Fin

/-- Appending two sequences v and w, and then extracting
the less than part, gives back the original first sequence v. -/
@[simp]
theorem append_apply_lt (v : Fin m → α) (w : Fin n → α) (i : Fin (m + n)) (h : ↑i < m)
    : append v w i = v ⟨↑i, h⟩ := by
  simp only [append, addCases, h, ↓reduceDIte]
  exact rfl

/-- Appending two sequences v and w, and then extracting
the greater than or equal part, gives back the original second sequence w. -/
@[simp]
theorem append_apply_ge (v : Fin m → α) (w : Fin n → α) (i : Fin (m + n)) (h : m ≤ ↑i)
    : append v w i = w ⟨↑i - m, Nat.sub_lt_left_of_lt_add h i.isLt⟩ := by
  simp only [append, addCases, eq_rec_constant]
  exact dif_neg (Nat.not_lt.mpr h)

/-- A property holds for all elements of an appended sequence iff
it holds for all elements of both original sequences -/
theorem append_forall_iff (P : α → Prop) (v1 : Fin m → α) (v2 : Fin n → α) :
    (∀ i, P (append v1 v2 i)) ↔ (∀ i, P (v1 i)) ∧ (∀ i, P (v2 i)) := by
  constructor
  · --bi-implication right-to-left part
    intro h
    constructor --conjunction
    · intro i
      have h2 : append v1 v2 (Fin.castAdd n i) = v1 i := by simp [append_apply_lt]
      rw [← h2]
      exact h _
    · intro i
      have h3 : append v1 v2 (Fin.natAdd m i) = v2 i := by
        simp
      rw [← h3]
      exact h _
  · --bi-implication left-to-right part
    intro ⟨h1, h2⟩ i
    -- deconstruct the appended sequence
    rcases lt_or_ge i.val m with hi_lt | hi_ge
    · rw [append_apply_lt v1 v2 i hi_lt]
      exact h1 ⟨i.val, hi_lt⟩
    · rw [append_apply_ge v1 v2 i hi_ge]
      exact h2 ⟨i.val - m, Nat.sub_lt_left_of_lt_add hi_ge i.isLt⟩

/-- Appending two sequences of elements from s produces a sequence of elements from s -/
theorem append_mem (s : Set α) (v1 : Fin m → α) (v2 : Fin n → α)
    (h1 : ∀ i, v1 i ∈ s) (h2 : ∀ i, v2 i ∈ s) :
    (∀ i, (append v1 v2) i ∈ s) :=
  (append_forall_iff (· ∈ s) v1 v2).mpr ⟨h1, h2⟩

end Fin
