/-
Copyright (c) 2021 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys

! This file was ported from Lean 3 source module imo.imo2021_q1
! leanprover-community/mathlib commit 308826471968962c6b59c7ff82a22757386603e3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Sqrt
import Mathbin.Tactic.IntervalCases
import Mathbin.Tactic.Linarith.Default
import Mathbin.Tactic.NormCast
import Mathbin.Tactic.NormNum
import Mathbin.Tactic.RingExp

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

    a = 2 * l * l - 4 * l
    b = 2 * l * l + 1
    c = 2 * l * l + 4 * l

Therefore, it is enough to show that there exists a natural number l such that
`n ≤ 2 * l * l - 4 * l` and `2 * l * l + 4 * l ≤ 2 * n` for `n ≥ 100`.

Then, by the Pigeonhole principle, at least two numbers in the triplet must lie in the same pile,
which finishes the proof.
-/


open Real

namespace imo2021_q1

theorem lower_bound (n l : ℕ) (hl : 2 + sqrt (4 + 2 * n) ≤ 2 * l) : n + 4 * l ≤ 2 * l * l :=
  by
  suffices 2 * ((n : ℝ) + 4 * l) - 8 * l + 4 ≤ 2 * (2 * l * l) - 8 * l + 4
    by
    simp only [mul_le_mul_left, sub_le_sub_iff_right, add_le_add_iff_right, zero_lt_two] at this 
    exact_mod_cast this
  rw [← le_sub_iff_add_le', sqrt_le_iff, pow_two] at hl 
  convert hl.2 using 1 <;> ring
#align imo2021_q1.lower_bound Imo2021Q1.lower_bound

theorem upper_bound (n l : ℕ) (hl : (l : ℝ) ≤ sqrt (1 + n) - 1) : 2 * l * l + 4 * l ≤ 2 * n :=
  by
  have h1 : ∀ n : ℕ, 0 ≤ 1 + (n : ℝ) := by intro n; exact_mod_cast Nat.zero_le (1 + n)
  rw [le_sub_iff_add_le', le_sqrt (h1 l) (h1 n), pow_two] at hl 
  rw [← add_le_add_iff_right 2, ← @Nat.cast_le ℝ]
  simp only [Nat.cast_bit0, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
  convert (mul_le_mul_left zero_lt_two).mpr hl using 1 <;> ring
#align imo2021_q1.upper_bound Imo2021Q1.upper_bound

theorem radical_inequality {n : ℕ} (h : 107 ≤ n) : sqrt (4 + 2 * n) ≤ 2 * (sqrt (1 + n) - 3) :=
  by
  have h1n : 0 ≤ 1 + (n : ℝ) := by norm_cast; exact Nat.zero_le _
  rw [sqrt_le_iff]
  constructor
  · simp only [sub_nonneg, zero_le_mul_left, zero_lt_two, le_sqrt zero_lt_three.le h1n]
    norm_cast; linarith only [h]
  ring
  rw [pow_two, ← sqrt_mul h1n, sqrt_mul_self h1n]
  suffices 24 * sqrt (1 + n) ≤ 2 * n + 36 by linarith
  rw [mul_self_le_mul_self_iff]
  swap; · norm_num; apply sqrt_nonneg
  swap; · norm_cast; linarith
  ring
  rw [pow_two, ← sqrt_mul h1n, sqrt_mul_self h1n]
  -- Not splitting into cases lead to a deterministic timeout on my machine
  obtain ⟨rfl, h'⟩ : 107 = n ∨ 107 < n := eq_or_lt_of_le h
  · norm_num
  · norm_cast
    nlinarith
#align imo2021_q1.radical_inequality Imo2021Q1.radical_inequality

-- We will later make use of the fact that there exists (l : ℕ) such that
-- n ≤ 2 * l * l - 4 * l and 2 * l * l + 4 * l ≤ 2 * n for n ≥ 107.
theorem exists_numbers_in_interval (n : ℕ) (hn : 107 ≤ n) :
    ∃ l : ℕ, n + 4 * l ≤ 2 * l * l ∧ 2 * l * l + 4 * l ≤ 2 * n :=
  by
  rsuffices ⟨l, t⟩ : ∃ l : ℕ, 2 + sqrt (4 + 2 * n) ≤ 2 * (l : ℝ) ∧ (l : ℝ) ≤ sqrt (1 + n) - 1
  · exact ⟨l, lower_bound n l t.1, upper_bound n l t.2⟩
  let x := sqrt (1 + n) - 1
  refine' ⟨⌊x⌋₊, _, _⟩
  · trans 2 * (x - 1)
    · dsimp only [x]; linarith only [radical_inequality hn]
    · simp only [mul_le_mul_left, zero_lt_two]; linarith only [(Nat.lt_floor_add_one x).le]
  · apply Nat.floor_le; rw [sub_nonneg, le_sqrt]
    all_goals norm_cast; simp only [one_pow, le_add_iff_nonneg_right, zero_le']
#align imo2021_q1.exists_numbers_in_interval Imo2021Q1.exists_numbers_in_interval

theorem exists_triplet_summing_to_squares (n : ℕ) (hn : 100 ≤ n) :
    ∃ a b c : ℕ,
      n ≤ a ∧
        a < b ∧
          b < c ∧
            c ≤ 2 * n ∧
              (∃ k : ℕ, a + b = k * k) ∧ (∃ l : ℕ, c + a = l * l) ∧ ∃ m : ℕ, b + c = m * m :=
  by
  -- If n ≥ 107, we do not explicitly construct the triplet but use an existence
  -- argument from lemma above.
  obtain p | p : 107 ≤ n ∨ n < 107 := le_or_lt 107 n
  · obtain ⟨l, hl1, hl2⟩ := exists_numbers_in_interval n p
    have p : 1 < l := by contrapose! hl1; interval_cases <;> linarith
    have h₁ : 4 * l ≤ 2 * l * l := by linarith
    have h₂ : 1 ≤ 2 * l := by linarith
    refine'
      ⟨2 * l * l - 4 * l, 2 * l * l + 1, 2 * l * l + 4 * l, _, _, _,
        ⟨_, ⟨2 * l - 1, _⟩, ⟨2 * l, _⟩, 2 * l + 1, _⟩⟩
    all_goals zify [h₁, h₂]; linarith
  -- Otherwise, if 100 ≤ n < 107, then it suffices to consider explicit
  -- construction of a triplet {a, b, c}, which is constructed by setting l=9
  -- in the argument at the start of the file.
  · refine' ⟨126, 163, 198, p.le.trans _, _, _, _, ⟨17, _⟩, ⟨18, _⟩, 19, _⟩
    pick_goal 4; · linarith
    all_goals norm_num
#align imo2021_q1.exists_triplet_summing_to_squares Imo2021Q1.exists_triplet_summing_to_squares

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (a b «expr ∈ » B) -/
-- Since it will be more convenient to work with sets later on, we will translate the above claim
-- to state that there always exists a set B ⊆ [n, 2n] of cardinality at least 3, such that each
-- pair of pairwise unequal elements of B sums to a perfect square.
theorem exists_finset_3_le_card_with_pairs_summing_to_squares (n : ℕ) (hn : 100 ≤ n) :
    ∃ B : Finset ℕ,
      2 * 1 + 1 ≤ B.card ∧
        (∀ (a) (_ : a ∈ B) (b) (_ : b ∈ B), a ≠ b → ∃ k, a + b = k * k) ∧
          ∀ c ∈ B, n ≤ c ∧ c ≤ 2 * n :=
  by
  obtain ⟨a, b, c, hna, hab, hbc, hcn, h₁, h₂, h₃⟩ := exists_triplet_summing_to_squares n hn
  refine' ⟨{a, b, c}, _, _, _⟩
  · suffices ({a, b, c} : Finset ℕ).card = 3 by rw [this]; exact le_rfl
    suffices a ∉ {b, c} ∧ b ∉ {c} by
      rw [Finset.card_insert_of_not_mem this.1, Finset.card_insert_of_not_mem this.2,
        Finset.card_singleton]
    · rw [Finset.mem_insert, Finset.mem_singleton, Finset.mem_singleton]
      push_neg
      exact ⟨⟨hab.ne, (hab.trans hbc).Ne⟩, hbc.ne⟩
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

end imo2021_q1

open imo2021_q1

/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (A «expr ⊆ » finset.Icc[finset.Icc] n «expr * »(2, n)) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (a b «expr ∈ » A) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:638:2: warning: expanding binder collection (a b «expr ∈ » «expr \ »(finset.Icc[finset.Icc] n «expr * »(2, n), A)) -/
theorem imo2021_q1 :
    ∀ n : ℕ,
      100 ≤ n →
        ∀ (A) (_ : A ⊆ Finset.Icc n (2 * n)),
          (∃ (a : _) (_ : a ∈ A) (b : _) (_ : b ∈ A), a ≠ b ∧ ∃ k : ℕ, a + b = k * k) ∨
            ∃ (a : _) (_ : a ∈ Finset.Icc n (2 * n) \ A) (b : _) (_ : b ∈ Finset.Icc n (2 * n) \ A),
              a ≠ b ∧ ∃ k : ℕ, a + b = k * k :=
  by
  intro n hn A hA
  -- For each n ∈ ℕ such that 100 ≤ n, there exists a pairwise unequal triplet {a, b, c} ⊆ [n, 2n]
  -- such that all pairwise sums are perfect squares. In practice, it will be easier to use
  -- a finite set B ⊆ [n, 2n] such that all pairwise unequal pairs of B sum to a perfect square
  -- noting that B has cardinality greater or equal to 3, by the explicit construction of the
  -- triplet {a, b, c} before.
  obtain ⟨B, hB, h₁, h₂⟩ := exists_finset_3_le_card_with_pairs_summing_to_squares n hn
  have hBsub : B ⊆ Finset.Icc n (2 * n) := by intro c hcB;
    simpa only [Finset.mem_Icc] using h₂ c hcB
  have hB' : 2 * 1 < (B ∩ (Finset.Icc n (2 * n) \ A) ∪ B ∩ A).card :=
    by
    rw [← Finset.inter_distrib_left, Finset.sdiff_union_self_eq_union,
      finset.union_eq_left_iff_subset.mpr hA, (Finset.inter_eq_left_iff_subset _ _).mpr hBsub]
    exact nat.succ_le_iff.mp hB
  -- Since B has cardinality greater or equal to 3, there must exist a subset C ⊆ B such that
  -- for any A ⊆ [n, 2n], either C ⊆ A or C ⊆ [n, 2n] \ A and C has cardinality greater
  -- or equal to 2.
  obtain ⟨C, hC, hCA⟩ := Finset.exists_subset_or_subset_of_two_mul_lt_card hB'
  rw [Finset.one_lt_card] at hC 
  rcases hC with ⟨a, ha, b, hb, hab⟩
  simp only [Finset.subset_iff, Finset.mem_inter] at hCA 
  -- Now we split into the two cases C ⊆ [n, 2n] \ A and C ⊆ A, which can be dealt with identically.
      cases hCA <;>
      [right; left] <;>
    exact ⟨a, (hCA ha).2, b, (hCA hb).2, hab, h₁ a (hCA ha).1 b (hCA hb).1 hab⟩
#align imo2021_q1 imo2021_q1

