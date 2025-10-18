/-
Copyright (c) 2024 Tomaz Mascarenhas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
/-!
# Timed Split
  This file defines some new lemmas related to the `List.split` function that are necessary
  for proving the complexity of `List.mergeSort`.
## Main Results
  - Timed.split_halves_length :
      ∀ l l₁ l₂ : list α, Timed.split l = (l₁, l₂) →
        l₁.length ≤ (l.length + 1) / 2 ∧ l₂.length ≤ l.length / 2
  - Timed.split_lengths :
      ∀ l l₁ l₂ : list α, Timed.split l = (l₁, l₂) →
        l₁.length + l₂.length = l.length
-/

namespace Timed

universe u

variable {α : Type u}

lemma div_two (b a : ℕ) : 2 * a ≤ b → a ≤ b / 2 :=
  by simp_rw [Nat.le_div_iff_mul_le zero_lt_two, mul_comm, imp_self]

lemma split_halves_length_aux : ∀ {l l₁ l₂ : List α},
  List.split l = (l₁, l₂) →
    2 * List.length l₁ ≤ List.length l + 1 ∧ 2 * List.length l₂ ≤ List.length l
  | []       => by
    intros h
    unfold List.split at h
    simp at h
    have ⟨h₁, h₂⟩ := h
    rw [← h₁, ← h₂]
    simp
  | (a :: t) => by
    intros h'
    cases e: List.split t with
    | mk t₁ t₂ =>
      have split_id : List.split (a :: t) = (a :: t₂, t₁) := by
        unfold List.split
        rw [e]
      rw [split_id] at h'
      injection h' with h₁ h₂
      have ⟨ih₁, ih₂⟩ := split_halves_length_aux e
      apply And.intro
      · rw [← h₁]
        simp
        linarith
      · rw [← h₂]
        simp [ih₁]

theorem split_halves_length : ∀ {l l₁ l₂ : List α},
  List.split l = (l₁, l₂) →
    List.length l₁ ≤ (List.length l + 1) / 2 ∧
    List.length l₂ ≤ (List.length l) / 2 := by
  intros l l₁ l₂ h
  have ⟨pf₁, pf₂⟩ := split_halves_length_aux h
  exact ⟨div_two (l.length + 1) l₁.length pf₁, div_two l.length l₂.length pf₂⟩

theorem split_lengths : ∀ (l l₁ l₂ : List α),
    List.split l = (l₁, l₂) → l₁.length + l₂.length = l.length
  | []  => by
    intros l₁ l₂
    simp
    intros h₁ h₂
    rw [← h₁, ← h₂]
    simp
  | [_] => by
    intros l₁ l₂
    simp
    intros h₁ h₂
    rw [← h₁, ← h₂]
    simp
  | (_ :: _ :: t) => by
    intros l₁ l₂ h
    cases e : List.split t with
    | mk l₁' l₂' =>
      simp at h
      rw [e] at h
      have ih := split_lengths t l₁' l₂' e
      have ⟨h₁, h₂⟩ := h
      rw [← h₁, ← h₂]
      simp
      linarith

end Timed
