/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Powerset

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
    (∃ t : Finset (Fin n), r < #t ∧ StrictMonoOn f ↑t) ∨
      ∃ t : Finset (Fin n), s < #t ∧ StrictAntiOn f ↑t := by
  -- Given an index `i`, produce the set of increasing (resp., decreasing) subsequences which ends
  -- at `i`.
  let inc_sequences_ending_in (i : Fin n) : Finset (Finset (Fin n)) :=
    univ.powerset.filter fun t => Finset.max t = i ∧ StrictMonoOn f ↑t
  let dec_sequences_ending_in (i : Fin n) : Finset (Finset (Fin n)) :=
    univ.powerset.filter fun t => Finset.max t = i ∧ StrictAntiOn f ↑t
  -- The singleton sequence is in both of the above collections.
  -- (This is useful to show that the maximum length subsequence is at least 1, and that the set
  -- of subsequences is nonempty.)
  have inc_i (i) : {i} ∈ inc_sequences_ending_in i := by
    simp [inc_sequences_ending_in, StrictMonoOn]
  have dec_i (i) : {i} ∈ dec_sequences_ending_in i := by
    simp [dec_sequences_ending_in, StrictAntiOn]
  -- Define the pair of labels: at index `i`, the pair is the maximum length of an increasing
  -- subsequence ending at `i`, paired with the maximum length of a decreasing subsequence ending
  -- at `i`.
  -- We call these labels `(a_i, b_i)`.
  let ab (i : Fin n) : ℕ × ℕ :=
    (max' ((inc_sequences_ending_in i).image card) (Nonempty.image ⟨{i}, inc_i i⟩ _),
      max' ((dec_sequences_ending_in i).image card) (Nonempty.image ⟨{i}, dec_i i⟩ _))
  -- It now suffices to show that one of the labels is 'big' somewhere. In particular, if the
  -- first in the pair is more than `r` somewhere, then we have an increasing subsequence in our
  -- set, and if the second is more than `s` somewhere, then we have a decreasing subsequence.
  have hab1 (i : Fin n) : (ab i).1 ∈ image card (inc_sequences_ending_in i) := by
    simpa only [ab] using max'_mem _ _
  have hab2 (i : Fin n) : (ab i).2 ∈ image card (dec_sequences_ending_in i) := by
    simpa only [ab] using max'_mem _ _
  rsuffices ⟨i, hi⟩ : ∃ i, r < (ab i).1 ∨ s < (ab i).2
  · refine hi.imp ?_ ?_
    on_goal 1 => have := hab1 i
    on_goal 2 => have := hab2 i
    all_goals
      intro hi
      rw [mem_image] at this
      obtain ⟨t, ht₁, ht₂⟩ := this
      refine ⟨t, by rwa [ht₂], ?_⟩
      rw [mem_filter] at ht₁
      apply ht₁.2.2
  -- Show first that the pair of labels is unique.
  have : Injective ab := by
    apply injective_of_lt_imp_ne
    intro i j k q
    injection q with q₁ q₂
    -- We have two cases: `f i < f j` or `f j < f i`.
    -- In the former we'll show `a_i < a_j`, and in the latter we'll show `b_i < b_j`.
    cases lt_or_gt_of_ne fun _ => ne_of_lt ‹i < j› (hf ‹f i = f j›)
    on_goal 1 =>
      apply ne_of_lt _ q₁
      have := hab1 i
    on_goal 2 =>
      apply ne_of_lt _ q₂
      have := hab2 i
    all_goals
      -- Reduce to showing there is a subsequence of length `a_i + 1` which ends at `j`.
      rw [Nat.lt_iff_add_one_le]
      apply le_max'
      rw [mem_image] at this ⊢
      -- In particular we take the subsequence `t` of length `a_i` which ends at `i`, by definition
      -- of `a_i`
      rcases this with ⟨t, ht₁, ht₂⟩
      rw [mem_filter] at ht₁
      -- Ensure `t` ends at `i`.
      have : t.max = i := by simp only [ht₁.2.1]
      -- Now our new subsequence is given by adding `j` at the end of `t`.
      refine ⟨insert j t, ?_, ?_⟩
      -- First make sure it's valid, i.e., that this subsequence ends at `j` and is increasing
      · rw [mem_filter]
        refine ⟨?_, ?_, ?_⟩
        · rw [mem_powerset]; apply subset_univ
        -- It ends at `j` since `i < j`.
        · convert max_insert (a := j) (s := t)
          rw [ht₁.2.1, max_eq_left]
          apply WithBot.coe_le_coe.mpr (le_of_lt ‹i < j›)
        -- To show it's increasing (i.e., `f` is monotone increasing on `t.insert j`), we do cases
        -- on what the possibilities could be - either in `t` or equals `j`.
        simp only [StrictMonoOn, StrictAntiOn, coe_insert, Set.mem_insert_iff, mem_coe]
        -- Most of the cases are just bashes.
        rintro x ⟨rfl | _⟩ y ⟨rfl | _⟩ _
        · apply (irrefl _ ‹j < j›).elim
        · exfalso
          apply not_le_of_gt (_root_.trans ‹i < j› ‹j < y›) (le_max_of_eq ‹y ∈ t› ‹t.max = i›)
        · first
          | apply lt_of_le_of_lt _ ‹f i < f j›
          | apply lt_of_lt_of_le ‹f j < f i› _
          rcases lt_or_eq_of_le (le_max_of_eq ‹x ∈ t› ‹t.max = i›) with (_ | rfl)
          · apply le_of_lt (ht₁.2.2 ‹x ∈ t› (mem_of_max ‹t.max = i›) ‹x < i›)
          · rfl
        · apply ht₁.2.2 ‹x ∈ t› ‹y ∈ t› ‹x < y›
      -- Finally show that this new subsequence is one longer than the old one.
      · rw [card_insert_of_notMem, ht₂]
        intro
        apply not_le_of_gt ‹i < j› (le_max_of_eq ‹j ∈ t› ‹t.max = i›)
  -- Finished both goals!
  -- Now that we have uniqueness of each label, it remains to do some counting to finish off.
  -- Suppose all the labels are small.
  by_contra! q
  -- Then the labels `(a_i, b_i)` all fit in the following set: `{ (x,y) | 1 ≤ x ≤ r, 1 ≤ y ≤ s }`
  let ran : Finset (ℕ × ℕ) := (range r).image Nat.succ ×ˢ (range s).image Nat.succ
  -- which we prove here.
  have : image ab univ ⊆ ran := by
    -- First some logical shuffling
    rintro ⟨x₁, x₂⟩
    simp only [ran, mem_image, mem_range, mem_univ, mem_product, true_and,
      Prod.ext_iff]
    rintro ⟨i, rfl, rfl⟩
    specialize q i
    -- Show `1 ≤ a_i` and `1 ≤ b_i`, which is easy from the fact that `{i}` is an increasing and
    -- decreasing subsequence which we did right near the top.
    have z : 1 ≤ (ab i).1 ∧ 1 ≤ (ab i).2 := by
      constructor <;>
        · apply le_max'
          rw [mem_image]
          exact ⟨{i}, by solve_by_elim, card_singleton i⟩
    -- Need to get `a_i ≤ r`, here phrased as: there is some `a < r` with `a+1 = a_i`.
    exact ⟨⟨(ab i).1 - 1, by omega⟩, (ab i).2 - 1, by omega⟩
  -- To get our contradiction, it suffices to prove `n ≤ r * s`
  apply not_le_of_gt hn
  -- Which follows from considering the cardinalities of the subset above, since `ab` is injective.
  simpa [ran, Nat.succ_injective, card_image_of_injective, ‹Injective ab›] using card_le_card this

end Theorems100
