/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Set.Monotone
import Mathlib.Order.Interval.Finset.Nat

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

namespace Theorems100

variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β] {f : α → β} {i : α}

/-- The possible lengths of an increasing sequence which ends at `i`. -/
private noncomputable def incSequencesTo (f : α → β) (i : α) : Finset ℕ :=
  open Classical in
  image card {t : Finset α | IsGreatest t i ∧ StrictMonoOn f t}

/-- The possible lengths of a decreasing sequence which ends at `i`. -/
private noncomputable def decSequencesTo (f : α → β) (i : α) : Finset ℕ :=
  open Classical in
  image card {t : Finset α | IsGreatest t i ∧ StrictAntiOn f t}

/-- The singleton sequence is increasing, so 1 is a possible length. -/
private lemma one_mem_incSequencesTo : 1 ∈ incSequencesTo f i := mem_image.2 ⟨{i}, by simp⟩
/-- The singleton sequence is decreasing, so 1 is a possible length. -/
private lemma one_mem_decSequencesTo : 1 ∈ decSequencesTo f i := one_mem_incSequencesTo (β := βᵒᵈ)

/-- The singleton sequence is increasing, so the set of lengths is nonempty. -/
private lemma incSequencesTo_nonempty : (incSequencesTo f i).Nonempty := ⟨1, one_mem_incSequencesTo⟩
/-- The singleton sequence is decreasing, so the set of lengths is nonempty. -/
private lemma decSequencesTo_nonempty : (decSequencesTo f i).Nonempty := ⟨1, one_mem_decSequencesTo⟩

/-- The maximum length of an increasing sequence which ends at `i`. -/
private noncomputable def maxIncSequencesTo (f : α → β) (i : α) : ℕ :=
  max' (incSequencesTo f i) incSequencesTo_nonempty

/-- The maximum length of a decreasing sequence which ends at `i`. -/
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

/--
We will want to show that if `i ≠ j`, then the pairs
`(maxIncSequencesTo f i, maxDecSequencesTo f i)` and
`(maxIncSequencesTo f j, maxDecSequencesTo f j)` are different.
To this end, we will assume wlog that `i < j`, and show that if `f i < f j`,
then `maxIncSequencesTo f i < maxIncSequencesTo f j`, and later dualise to prove that if `f j < f i`
then `maxDecSequencesTo f i < maxDecSequencesTo f j`.
-/
private lemma maxIncSequencesTo_lt {i j : α} (hij : i < j) (hfij : f i < f j) :
    maxIncSequencesTo f i < maxIncSequencesTo f j := by
  classical
  rw [Nat.lt_iff_add_one_le]
  refine le_max' _ _ ?_
  have : maxIncSequencesTo f i ∈ incSequencesTo f i := max'_mem _ incSequencesTo_nonempty
  simp only [incSequencesTo, mem_image, mem_filter, mem_univ, true_and, and_assoc] at this
  obtain ⟨t, hti, ht₁, ht₂⟩ := this
  simp only [incSequencesTo, mem_image, mem_filter, mem_univ, true_and, and_assoc]
  have : ∀ x ∈ t, x < j := by
    intro x hx
    exact (hti.2 hx).trans_lt hij
  refine ⟨insert j t, ?_, ?_, ?_⟩
  next =>
    convert hti.insert j using 1
    next => simp
    next => rw [max_eq_left hij.le]
  next =>
    simp only [coe_insert]
    rw [strictMonoOn_insert_iff_of_forall_le]
    · refine ⟨?_, ht₁⟩
      intro x hx hxj
      exact (ht₁.monotoneOn hx hti.1 (hti.2 hx)).trans_lt hfij
    · exact fun x hx ↦ (this x hx).le
  have : j ∉ t := fun hj ↦ lt_irrefl _ (this _ hj)
  simp [this, ht₂]

private lemma maxDecSequencesTo_gt {i j : α} (hij : i < j) (hfij : f j < f i) :
    maxDecSequencesTo f i < maxDecSequencesTo f j :=
  maxIncSequencesTo_lt (β := βᵒᵈ) hij hfij

/--
For each entry, we form a pair of labels consisting of the maximum lengths of increasing and
decreasing sequences ending there.
-/
private noncomputable def paired (f : α → β) (i : α) : ℕ × ℕ :=
  (maxIncSequencesTo f i, maxDecSequencesTo f i)

/--
By combining the previous two lemmas, we see that since `f` is injective, the pairs of labels
must also be unique.
-/
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
  -- It suffices to prove that there is some `i` where one of the max lengths is bigger than
  -- `r` or `s`, as this corresponds to a monotone sequence of the required length.
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
  -- If such an `i` does not exist, then our pairs of labels lie in a small set, which is a
  -- contradiction since the pairs are unique.
  by_contra! q
  have : Set.MapsTo (paired f) (univ : Finset α) (Icc 1 r ×ˢ Icc 1 s : Finset _) := by
    simp [paired, one_le_maxIncSequencesTo, one_le_maxDecSequencesTo, Set.MapsTo, *]
  refine hn.not_ge ?_
  simpa using card_le_card_of_injOn (paired f) this (paired_injective hf).injOn

end Theorems100
