/-
Copyright (c) 2021 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

#align_import imo.imo2021_q1 from "leanprover-community/mathlib"@"308826471968962c6b59c7ff82a22757386603e3"

/-!
# IMO 2021 Q1

Let `n≥100` be an integer. Ivan writes the numbers `n, n+1,..., 2n` each on different cards.
He then shuffles these `n+1` cards, and divides them into two piles. Prove that at least one
of the piles contains two cards such that the sum of their numbers is a perfect square.

# Solution

We show there exists a triplet `a, b, c ∈ [n , 2n]` with `a < b < c` and each of the sums `(a + b)`,
`(b + c)`, `(a + c)` being a perfect square. Specifically, we consider the linear system of
equations

    a + b = (2 * l - 1) ^ 2
    a + c = (2 * l) ^ 2
    b + c = (2 * l + 1) ^ 2

which can be solved to give

    a = 2 * l ^ 2 - 4 * l
    b = 2 * l ^ 2 + 1
    c = 2 * l ^ 2 + 4 * l

Therefore, it is enough to show that there exists a natural number l such that
`n ≤ 2 * l ^ 2 - 4 * l` and `2 * l ^ 2 + 4 * l ≤ 2 * n` for `n ≥ 100`.

Then, by the Pigeonhole principle, at least two numbers in the triplet must lie in the same pile,
which finishes the proof.
-/

open Finset

namespace Imo2021Q1

-- We will later make use of the fact that there exists (l : ℕ) such that
-- n ≤ 2 * l ^ 2 - 4 * l and 2 * l ^ 2 + 4 * l ≤ 2 * n for n ≥ 100.
theorem exists_numbers_in_interval (n : ℕ) (hn : 100 ≤ n) :
    ∃ l : ℕ, n + 4 * l ≤ 2 * l ^ 2 ∧ 2 * l ^ 2 + 4 * l ≤ 2 * n := by
  have hn' : 1 ≤ Nat.sqrt (n + 1) := by
    rw [Nat.le_sqrt]
    linarith
  have h₁ := Nat.sqrt_le' (n + 1)
  have h₂ := Nat.succ_le_succ_sqrt' (n + 1)
  have h₃ : 10 ≤ (n + 1).sqrt := by
    rw [Nat.le_sqrt]
    linarith only [hn]
  rw [← Nat.sub_add_cancel hn'] at h₁ h₂ h₃
  set l := (n + 1).sqrt - 1
  refine ⟨l, ?_, ?_⟩
  · calc n + 4 * l ≤ (l ^ 2 + 4 * l + 2) + 4 * l := by linarith only [h₂]
      _ ≤ 2 * l ^ 2 := by nlinarith only [h₃]
  · linarith only [h₁]
#align imo2021_q1.exists_numbers_in_interval Imo2021Q1.exists_numbers_in_interval

theorem exists_triplet_summing_to_squares (n : ℕ) (hn : 100 ≤ n) :
    ∃ a b c : ℕ, n ≤ a ∧ a < b ∧ b < c ∧ c ≤ 2 * n ∧
      (∃ k : ℕ, a + b = k ^ 2) ∧ (∃ l : ℕ, c + a = l ^ 2) ∧ ∃ m : ℕ, b + c = m ^ 2 := by
  obtain ⟨l, hl1, hl2⟩ := exists_numbers_in_interval n hn
  have p : 1 < l := by contrapose! hl1; interval_cases l <;> linarith
  have h₁ : 4 * l ≤ 2 * l ^ 2 := by linarith
  have h₂ : 1 ≤ 2 * l := by linarith
  refine ⟨2 * l ^ 2 - 4 * l, 2 * l ^ 2 + 1, 2 * l ^ 2 + 4 * l, ?_, ?_, ?_,
    ⟨?_, ⟨2 * l - 1, ?_⟩, ⟨2 * l, ?_⟩, 2 * l + 1, ?_⟩⟩
  all_goals zify [h₁, h₂]; linarith
#align imo2021_q1.exists_triplet_summing_to_squares Imo2021Q1.exists_triplet_summing_to_squares

-- Since it will be more convenient to work with sets later on, we will translate the above claim
-- to state that there always exists a set B ⊆ [n, 2n] of cardinality at least 3, such that each
-- pair of pairwise unequal elements of B sums to a perfect square.
theorem exists_finset_3_le_card_with_pairs_summing_to_squares (n : ℕ) (hn : 100 ≤ n) :
    ∃ B : Finset ℕ,
      2 * 1 + 1 ≤ B.card ∧
      (∀ a ∈ B, ∀ b ∈ B, a ≠ b → ∃ k, a + b = k ^ 2) ∧
      ∀ c ∈ B, n ≤ c ∧ c ≤ 2 * n := by
  obtain ⟨a, b, c, hna, hab, hbc, hcn, h₁, h₂, h₃⟩ := exists_triplet_summing_to_squares n hn
  refine ⟨{a, b, c}, ?_, ?_, ?_⟩
  · suffices ({a, b, c} : Finset ℕ).card = 3 by rw [this]
    suffices a ∉ {b, c} ∧ b ∉ {c} by
      rw [Finset.card_insert_of_not_mem this.1, Finset.card_insert_of_not_mem this.2,
        Finset.card_singleton]
    rw [Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton]
    push_neg
    exact ⟨⟨hab.ne, (hab.trans hbc).ne⟩, hbc.ne⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with (rfl | rfl | rfl) <;> rcases hy with (rfl | rfl | rfl)
    all_goals
      first
      | contradiction
      | assumption
      | simpa only [add_comm x y]
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro d (rfl | rfl | rfl) <;> constructor <;> linarith only [hna, hab, hbc, hcn]
#align imo2021_q1.exists_finset_3_le_card_with_pairs_summing_to_squares Imo2021Q1.exists_finset_3_le_card_with_pairs_summing_to_squares

end Imo2021Q1

open Imo2021Q1

theorem imo2021_q1 :
    ∀ n : ℕ, 100 ≤ n → ∀ A ⊆ Finset.Icc n (2 * n),
    (∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ ∃ k : ℕ, a + b = k ^ 2) ∨
    ∃ a ∈ Finset.Icc n (2 * n) \ A, ∃ b ∈ Finset.Icc n (2 * n) \ A,
      a ≠ b ∧ ∃ k : ℕ, a + b = k ^ 2 := by
  intro n hn A hA
  -- For each n ∈ ℕ such that 100 ≤ n, there exists a pairwise unequal triplet {a, b, c} ⊆ [n, 2n]
  -- such that all pairwise sums are perfect squares. In practice, it will be easier to use
  -- a finite set B ⊆ [n, 2n] such that all pairwise unequal pairs of B sum to a perfect square
  -- noting that B has cardinality greater or equal to 3, by the explicit construction of the
  -- triplet {a, b, c} before.
  obtain ⟨B, hB, h₁, h₂⟩ := exists_finset_3_le_card_with_pairs_summing_to_squares n hn
  have hBsub : B ⊆ Finset.Icc n (2 * n) := by
    intro c hcB; simpa only [Finset.mem_Icc] using h₂ c hcB
  have hB' : 2 * 1 < (B ∩ (Finset.Icc n (2 * n) \ A) ∪ B ∩ A).card := by
    rw [← inter_union_distrib_left, sdiff_union_self_eq_union, union_eq_left.2 hA,
      inter_eq_left.2 hBsub]
    exact Nat.succ_le_iff.mp hB
  -- Since B has cardinality greater or equal to 3, there must exist a subset C ⊆ B such that
  -- for any A ⊆ [n, 2n], either C ⊆ A or C ⊆ [n, 2n] \ A and C has cardinality greater
  -- or equal to 2.
  obtain ⟨C, hC, hCA⟩ := Finset.exists_subset_or_subset_of_two_mul_lt_card hB'
  rw [Finset.one_lt_card] at hC
  rcases hC with ⟨a, ha, b, hb, hab⟩
  simp only [Finset.subset_iff, Finset.mem_inter] at hCA
  -- Now we split into the two cases C ⊆ [n, 2n] \ A and C ⊆ A, which can be dealt with identically.
  cases' hCA with hCA hCA <;> [right; left] <;>
    exact ⟨a, (hCA ha).2, b, (hCA hb).2, hab, h₁ a (hCA ha).1 b (hCA hb).1 hab⟩
#align imo2021_q1 imo2021_q1
