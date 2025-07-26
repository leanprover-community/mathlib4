/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Appending finite sequences

We give various basic results regarding multiplying, appending,
and splitting finite sequences.

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
variable {E : Type*} [AddCommMonoid E]
variable {m n : ℕ}
variable (R : Type*) [Semiring R] [PartialOrder R]

namespace Fin

/-- Summing over appended v and w, and then extracting
the less than part, gives back the original first sequence v. -/
theorem sum_append (v : Fin m → E) (w : Fin n → E) :
    (∑ i, append v w i) = (∑ i, v i) + (∑ i, w i) := by
  simp [sum_univ_add]

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

/-- Appending two nonnegative sequences produces a nonnegative sequence -/
theorem append_nonneg (c1 : Fin m → R) (c2 : Fin n → R)
    (h1 : ∀ i, 0 ≤ c1 i) (h2 : ∀ i, 0 ≤ c2 i) :
    (∀ i : (Fin (m + n)), 0 ≤ (append c1 c2) i) :=
  (append_forall_iff (0 ≤ ·) c1 c2).mpr ⟨h1, h2⟩

variable (R : Type*) [Semiring R] [Module R E]

/-- Appending two scalar coefficient sequences
and two vector sequences by themselves, and then multiplying the appended sequences,
is equivalent to first multiplying the appropriate coefficients and vectors and then appending -/
theorem smul_append_distrib (c1 : Fin m → R) (v1 : Fin m → E)
    (c2 : Fin n → R) (v2 : Fin n → E) :
    (append c1 c2) • (append v1 v2) = append (c1 • v1) (c2 • v2) := by
  rw [append, append, append]
  ext ⟨i, hi⟩
  by_cases h : i < m
  · simp [addCases, h]
  · simp [addCases, h]


end Fin
