/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Set.Monotone
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Minimal
import Mathlib

/-!
# Erdős–Szekeres theorem

This file proves Theorem 73 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/), also
known as the Erdős–Szekeres theorem: given a sequence of more than `r * s` distinct
values, there is an increasing sequence of length longer than `r` or a decreasing sequence of length
longer than `s`.

We use the proof outlined at
https://en.wikipedia.org/wiki/Erdos-Szekeres_theorem#Pigeonhole_principle.

## Tags

sequences, increasing, decreasing, Ramsey, Erdos-Szekeres, Erdős–Szekeres, Erdős-Szekeres
-/

open Function Finset

lemma strictMonoOn_insert_iff_of_mem_upperBounds {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (s : Set α) (a : α) (ha : a ∈ upperBounds s) :
    StrictMonoOn f (insert a s) ↔ (∀ b ∈ s, b < a → f b < f a) ∧ StrictMonoOn f s := by
  rw [strictMonoOn_insert_iff]
  have : ∀ b ∈ s, a < b → f a < f b := by
    intro b hb hab
    cases (ha hb).not_gt hab
  aesop

lemma strictMonoOn_insert_iff_of_mem_lowerBounds {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (s : Set α) (a : α) (ha : a ∈ lowerBounds s) :
    StrictMonoOn f (insert a s) ↔ (∀ b ∈ s, a < b → f a < f b) ∧ StrictMonoOn f s := by
  rw [strictMonoOn_insert_iff]
  have : ∀ b ∈ s, b < a → f b < f a := by
    intro b hb hab
    cases (ha hb).not_gt hab
  aesop

lemma strictAntiOn_insert_iff_of_mem_upperBounds {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (s : Set α) (a : α) (ha : a ∈ upperBounds s) :
    StrictAntiOn f (insert a s) ↔ (∀ b ∈ s, b < a → f a < f b) ∧ StrictAntiOn f s := by
  rw [strictAntiOn_insert_iff]
  have : ∀ b ∈ s, a < b → f b < f a := by
    intro b hb hab
    cases (ha hb).not_gt hab
  aesop

lemma strictAntiOn_insert_iff_of_mem_lowerBounds {α β : Type*} [Preorder α] [Preorder β] (f : α → β)
    (s : Set α) (a : α) (ha : a ∈ lowerBounds s) :
    StrictAntiOn f (insert a s) ↔ (∀ b ∈ s, a < b → f b < f a) ∧ StrictAntiOn f s := by
  rw [strictAntiOn_insert_iff]
  have : ∀ b ∈ s, b < a → f a < f b := by
    intro b hb hab
    cases (ha hb).not_gt hab
  aesop

namespace Theorems100

variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β] {f : α → β} {i : α}

private noncomputable def incSequencesTo (f : α → β) (i : α) : Finset ℕ :=
  open Classical in
  image card {t : Finset α | IsGreatest t.toSet i ∧ StrictMonoOn f t}

private noncomputable def decSequencesTo (f : α → β) (i : α) : Finset ℕ :=
  open Classical in
  image card {t : Finset α | IsGreatest t.toSet i ∧ StrictAntiOn f t}

private lemma one_mem_incSequencesTo : 1 ∈ incSequencesTo f i := mem_image.2 ⟨{i}, by simp⟩
private lemma one_mem_decSequencesTo : 1 ∈ decSequencesTo f i := one_mem_incSequencesTo (β := βᵒᵈ)

private lemma incSequencesTo_nonempty : (incSequencesTo f i).Nonempty := ⟨1, one_mem_incSequencesTo⟩
private lemma decSequencesTo_nonempty : (decSequencesTo f i).Nonempty := ⟨1, one_mem_decSequencesTo⟩

private noncomputable def maxIncSequencesTo (f : α → β) (i : α) : ℕ :=
  max' (incSequencesTo f i) incSequencesTo_nonempty

private noncomputable def maxDecSequencesTo (f : α → β) (i : α) : ℕ :=
  max' (decSequencesTo f i) decSequencesTo_nonempty

private lemma one_le_maxIncSequencesTo : 1 ≤ maxIncSequencesTo f i :=
  le_max' _ _ one_mem_incSequencesTo
private lemma one_le_maxDecSequencesTo : 1 ≤ maxDecSequencesTo f i :=
  le_max' _ _ one_mem_decSequencesTo

private lemma maxIncSequencesTo_mem : maxIncSequencesTo f i ∈ incSequencesTo f i :=
  max'_mem _ incSequencesTo_nonempty
private lemma maxDecSequencesTo_mem : maxDecSequencesTo f i ∈ decSequencesTo f i :=
  max'_mem _ decSequencesTo_nonempty

private lemma maxIncSequencesTo_lt {i j : α} (hij : i < j) (hfij : f i < f j) :
    maxIncSequencesTo f i < maxIncSequencesTo f j := by
  classical
  rw [Nat.lt_iff_add_one_le]
  refine le_max' _ _ ?_
  have : maxIncSequencesTo f i ∈ incSequencesTo f i := max'_mem _ incSequencesTo_nonempty
  simp only [incSequencesTo, mem_image, mem_filter, exists_prop, mem_univ, exists_and_right,
    true_and, and_assoc] at this
  obtain ⟨t, hti, ht₁, ht₂⟩ := this
  simp only [incSequencesTo, mem_image, mem_filter, mem_univ, true_and, exists_and_right,
    and_assoc]
  have : ∀ x ∈ t, x < j := by
    intro x hx
    exact (hti.2 hx).trans_lt hij
  refine ⟨insert j t, ?_, ?_, ?_⟩
  next =>
    convert hti.insert j using 1
    next => simp
    next => rw [max_eq_left hij.le]
  next =>
    simp only [coe_insert, incSequencesTo, decSequencesTo]
    rw [strictMonoOn_insert_iff_of_mem_upperBounds]
    · refine ⟨?_, ?_⟩
      · intro x hx hxj
        exact (ht₁.monotoneOn hx hti.1 (hti.2 hx)).trans_lt hfij
      · exact ht₁
    · intro x hx
      exact (this x hx).le
  have : j ∉ t := by
    intro hj
    exact lt_irrefl _ (this _ hj)
  simp [this, ht₂]

private lemma maxDecSequencesTo_gt {i j : α} (hij : i < j) (hfij : f j < f i) :
    maxDecSequencesTo f i < maxDecSequencesTo f j :=
  maxIncSequencesTo_lt (β := βᵒᵈ) hij hfij

private noncomputable def paired (f : α → β) (i : α) : ℕ × ℕ :=
  (maxIncSequencesTo f i, maxDecSequencesTo f i)

private lemma paired_injective (hf : Injective f) : Injective (paired f) := by
  apply injective_of_lt_imp_ne
  intro i j hij q
  cases lt_or_gt_of_ne (hf.ne hij.ne)
  case inl h => exact (maxIncSequencesTo_lt hij h).ne congr($q.1)
  case inr h => exact (maxDecSequencesTo_gt hij h).ne congr($q.2)

/-- **Erdős–Szekeres Theorem**: Given a sequence of more than `r * s` distinct values, there is an
increasing sequence of length longer than `r` or a decreasing sequence of length longer than `s`.

Proof idea:
We label each value in the sequence with two numbers specifying the longest increasing
subsequence ending there, and the longest decreasing subsequence ending there.
We then show the pair of labels must be unique. Now if there is no increasing sequence longer than
`r` and no decreasing sequence longer than `s`, then there are at most `r * s` possible labels,
which is a contradiction if there are more than `r * s` elements.
-/
theorem erdos_szekeres {r s : ℕ} {f : α → β} (hn : r * s < Fintype.card α) (hf : Injective f) :
    (∃ t : Finset α, r < #t ∧ StrictMonoOn f t) ∨
      ∃ t : Finset α, s < #t ∧ StrictAntiOn f t := by
  classical
  rsuffices ⟨i, hi⟩ : ∃ i, r < maxIncSequencesTo f i ∨ s < maxDecSequencesTo f i
  · refine Or.imp ?_ ?_ hi
    on_goal 1 =>
      have : maxIncSequencesTo f i ∈ image card _ := maxIncSequencesTo_mem
    on_goal 2 =>
      have : maxDecSequencesTo f i ∈ image card _ := maxDecSequencesTo_mem
    all_goals
      intro hi
      obtain ⟨t, ht₁, ht₂⟩ := mem_image.1 this
      refine ⟨t, by rwa [ht₂], ?_⟩
      rw [mem_filter] at ht₁
      exact ht₁.2.2
  by_contra! q
  have : Set.MapsTo (paired f) Finset.univ.toSet (Finset.Icc 1 r ×ˢ Finset.Icc 1 s).toSet := by
    simp [paired, one_le_maxIncSequencesTo, one_le_maxDecSequencesTo, *]
  refine hn.not_ge ?_
  simpa using card_le_card_of_injOn (paired f) this (paired_injective hf).injOn

end Theorems100
