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

variable {α : Type*} [LinearOrder α] {β : Type*}

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

/-- **Erdős–Szekeres Theorem**: Given a sequence of more than `r * s` distinct values, there is an
increasing sequence of length longer than `r` or a decreasing sequence of length longer than `s`.

Proof idea:
We label each value in the sequence with two numbers specifying the longest increasing
subsequence ending there, and the longest decreasing subsequence ending there.
We then show the pair of labels must be unique. Now if there is no increasing sequence longer than
`r` and no decreasing sequence longer than `s`, then there are at most `r * s` possible labels,
which is a contradiction if there are more than `r * s` elements.
-/
theorem erdos_szekeres {r s n : ℕ} {f : Fin n → α} (hn : r * s < n) (hf : Injective f) :
    (∃ t : Finset (Fin n), r < t.card ∧ StrictMonoOn f t) ∨
      ∃ t : Finset (Fin n), s < t.card ∧ StrictAntiOn f t := by
  classical
  -- Given an index `i`, produce the set of increasing (resp., decreasing) subsequences which ends
  -- at `i`.
  let inc_sequences_ending_in' (i : Fin n) : Finset ℕ := image card
    {t : Finset (Fin n) | IsGreatest t i ∧ StrictMonoOn f t}
  let dec_sequences_ending_in' (i : Fin n) : Finset ℕ := image card
    {t : Finset (Fin n) | IsGreatest t i ∧ StrictAntiOn f t}
  -- The singleton sequence is in both of the above collections.
  -- (This is useful to show that the maximum length subsequence is at least 1, and that the set
  -- of subsequences is nonempty.)
  have inc_i' (i : Fin n) : 1 ∈ inc_sequences_ending_in' i := by
    simp only [inc_sequences_ending_in', mem_image]
    use {i}
    simp
  have dec_i' (i : Fin n) : 1 ∈ dec_sequences_ending_in' i := by
    simp only [dec_sequences_ending_in', mem_image]
    use {i}
    simp
  -- Define the pair of labels: at index `i`, the pair is the maximum length of an increasing
  -- subsequence ending at `i`, paired with the maximum length of a decreasing subsequence ending
  -- at `i`.
  -- We call these labels `(a_i, b_i)`.
  let a (i : Fin n) : ℕ := max' (inc_sequences_ending_in' i) ⟨_, inc_i' i⟩
  let b (i : Fin n) : ℕ := max' (dec_sequences_ending_in' i) ⟨_, dec_i' i⟩
  have one_le_a (i) : 1 ≤ a i := le_max' _ _ (inc_i' _)
  have one_le_b (i) : 1 ≤ b i := le_max' _ _ (dec_i' _)
  have uniq_a : ∀ i j : Fin n, i < j → f i < f j → a i < a j := by
    intro i j hij hfij
    rw [Nat.lt_iff_add_one_le]
    refine le_max' _ _ ?_
    have : a i ∈ inc_sequences_ending_in' i := max'_mem _ ⟨_, inc_i' i⟩
    simp only [inc_sequences_ending_in', mem_image, mem_filter, exists_prop, mem_univ,
      exists_and_right, true_and, and_assoc] at this
    obtain ⟨t, hti, ht₁, ht₂⟩ := this
    simp only [inc_sequences_ending_in', mem_image, mem_filter, mem_univ, true_and,
      exists_and_right, and_assoc]
    have : ∀ x ∈ t, x < j := by
      intro x hx
      exact (hti.2 hx).trans_lt hij
    refine ⟨insert j t, ?_, ?_, ?_⟩
    next =>
      convert hti.insert j using 1
      next => simp
      next => rw [max_eq_left hij.le]
    next =>
      simp only [coe_insert, inc_sequences_ending_in', dec_sequences_ending_in']
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
  have uniq_b : ∀ i j : Fin n, i < j → f j < f i → b i < b j := by
    intro i j hij hfij
    rw [Nat.lt_iff_add_one_le]
    refine le_max' _ _ ?_
    have : b i ∈ dec_sequences_ending_in' i := max'_mem _ ⟨_, dec_i' i⟩
    simp only [dec_sequences_ending_in', mem_image, mem_filter, exists_prop, mem_univ,
      exists_and_right, true_and, and_assoc] at this
    obtain ⟨t, hti, ht₁, ht₂⟩ := this
    simp only [dec_sequences_ending_in', mem_image, mem_filter, mem_univ, true_and,
      exists_and_right, and_assoc]
    have : ∀ x ∈ t, x < j := by
      intro x hx
      exact (hti.2 hx).trans_lt hij
    refine ⟨insert j t, ?_, ?_, ?_⟩
    next =>
      convert hti.insert j using 1
      next => simp
      next => rw [max_eq_left hij.le]
    next =>
      simp only [coe_insert, inc_sequences_ending_in', dec_sequences_ending_in']
      rw [strictAntiOn_insert_iff_of_mem_upperBounds]
      · refine ⟨?_, ?_⟩
        · intro x hx hxj
          exact hfij.trans_le (ht₁.antitoneOn hx hti.1 (hti.2 hx))
        · exact ht₁
      · intro x hx
        exact (this x hx).le
    have : j ∉ t := by
      intro hj
      exact lt_irrefl _ (this _ hj)
    simp [this, ht₂]
  -- Show first that the pair of labels is unique.
  have hab : Injective (fun i ↦ (a i, b i)) := by
    apply injective_of_lt_imp_ne
    intro i j hij q
    -- We have two cases: `f i < f j` or `f j < f i`.
    -- In the former we'll show `a_i < a_j`, and in the latter we'll show `b_i < b_j`.
    cases lt_or_gt_of_ne fun _ => ne_of_lt ‹i < j› (hf ‹f i = f j›)
    case inl h => exact (uniq_a i j hij h).ne congr($q.1)
    case inr h => exact (uniq_b i j hij h).ne congr($q.2)
  -- It now suffices to show that one of the labels is 'big' somewhere. In particular, if the
  -- first in the pair is more than `r` somewhere, then we have an increasing subsequence in our
  -- set, and if the second is more than `s` somewhere, then we have a decreasing subsequence.
  rsuffices ⟨i, hi⟩ : ∃ i, r < a i ∨ s < b i
  · refine Or.imp ?_ ?_ hi
    on_goal 1 =>
      have : a i ∈ inc_sequences_ending_in' i := max'_mem _ ⟨_, inc_i' _⟩
    on_goal 2 =>
      have : b i ∈ dec_sequences_ending_in' i := max'_mem _ ⟨_, dec_i' _⟩
    all_goals
      intro hi
      rw [mem_image] at this
      obtain ⟨t, ht₁, ht₂⟩ := this
      refine ⟨t, by rwa [ht₂], ?_⟩
      rw [mem_filter] at ht₁
      apply ht₁.2.2
  -- Finished both goals!
  -- Now that we have uniqueness of each label, it remains to do some counting to finish off.
  -- Suppose all the labels are small.
  by_contra! q
  -- Then the labels `(a_i, b_i)` all fit in the following set: `{ (x,y) | 1 ≤ x ≤ r, 1 ≤ y ≤ s }`
  let ran : Finset (ℕ × ℕ) := Finset.Icc (1, 1) (r, s)
  -- -- which we prove here.
  have : univ.image (fun i ↦ (a i, b i)) ⊆ ran := by
    rintro ⟨x₁, x₂⟩
    simp +contextual only [mem_image, mem_univ, true_and, mem_Icc, forall_exists_index, ran,
      Prod.ext_iff]
    rintro i ⟨rfl, rfl⟩
    exact ⟨⟨one_le_a _, one_le_b _⟩, q _⟩
  -- To get our contradiction, it suffices to prove `n ≤ r * s`
  apply not_le_of_gt hn
  -- Which follows from considering the cardinalities of the subset above, since `ab` is injective.
  simpa [ran, card_image_of_injective, ‹Injective _›, Finset.card_Icc_prod] using card_le_card this

end Theorems100
