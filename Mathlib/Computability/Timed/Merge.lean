/-
Copyright (c) 2024 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/
import Mathlib.Tactic.Linarith
/-!
# Timed Merge

This file defines a new version of Merge that, besides combining the input lists, counts the
number of operations made through the execution of the algorithm. Also, it presents proofs of
its time complexity and it's equivalence to the one defined in Data/List/Sort.lean

## Main Definition

- Timed.merge : list α → list α → (list α × ℕ)

## Main Results

- Timed.merge_complexity : ∀ l₁ l₂, (Timed.merge l₁ l₂).snd ≤ l₁.length + l₂.length
- Timed.merge_equivalence : ∀ l₁ l₂, (Timed.merge l₁ l₂).fst = List.merge l₁ l₂
-/

namespace Timed

universe u

variable {α : Type u} (s : α → α → Bool)
local infixl:50 " ≼ " => s

/-- The redesigned version of `merge`, which also returns the number of comparisons
performed. -/
def merge (xs ys : List α) (le : α → α → Bool := by exact fun a b => a ≤ b) : List α × ℕ :=
  match xs, ys with
  | [], ys => (ys, 0)
  | xs, [] => (xs, 0)
  | x :: xs, y :: ys =>
    if le x y then
      let (l, n) := merge xs (y :: ys) le
      (x :: l, n + 1)
    else
      let (l, n) := merge (x :: xs) ys le
      (y :: l, n + 1)

theorem merge_complexity : ∀ l₁ l₂ : List α,
    (merge l₁ l₂ s).snd ≤ l₁.length + l₂.length
  | [], l₂ => by simp [merge]
  | (h₁ :: t₁), [] => by simp [merge]
  | (h₁ :: t₁), (h₂ :: t₂) => by
    unfold merge
    cases s h₁ h₂
    · have ih := merge_complexity (h₁ :: t₁) t₂
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons, ge_iff_le] at ih ⊢
      linarith
    · have ih := merge_complexity t₁ (h₂ :: t₂)
      simp only [↓reduceIte, List.length_cons, ge_iff_le] at ih ⊢
      linarith

theorem merge_equivalence : ∀ l₁ l₂ : List α,
    (merge l₁ l₂ s).fst = List.merge l₁ l₂ s
  | [],       [] => by simp [merge]
  | [],       (h₂ :: t₂) => by simp [merge]
  | (h₁ :: t₁), [] => by simp [merge]
  | (h₁ :: t₁), (h₂ :: t₂) => by
    unfold merge
    unfold List.merge
    cases s h₁ h₂
    · simp only [Bool.false_eq_true, ↓reduceIte, List.cons.injEq, true_and]
      rw [merge_equivalence (h₁ :: t₁) t₂]
    · simp only [Bool.false_eq_true, ↓reduceIte, List.cons.injEq, true_and]
      rw [merge_equivalence t₁ (h₂ :: t₂)]

end Timed
