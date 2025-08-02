/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Group.Int.Sum
import Mathlib.Algebra.Order.Ring.Int

/-!
# IMO 2015 Q6

The sequence $a_1, a_2, \dots$ of integers satisfies the conditions

1. $1 ≤ a_j ≤ 2015$ for all $j ≥ 1$,
2. $k + a_k ≠ l + a_l$ for all $1 ≤ k < l$.

Prove that there exist two positive integers $b$ and $N$ for which
$$\left|\sum_{j=m+1}^n (a_j-b)\right| ≤ 1007^2$$
for all integers $m,n$ such that $N ≤ m < n$.

# Solution

We follow solution 2 ("juggling") from https://web.evanchen.cc/exams/IMO-2015-notes.pdf.

Consider a collection of balls at different integer heights that starts out empty at time 0
and is modified at each succeeding integer time `t` as follows:

* If there is a ball at height 0 it is removed (caught)
* Then a ball is added at height $a_t$
* Then all balls have their height decreased by 1

Condition 1 ensures that all heights stay in [0, 2014]. Condition 2 ensures that the heights at any
point in time are distinct, so we can model the collection as a finset of heights of monotonically
increasing, bounded cardinality. So there is a time where the cardinality reaches a maximum;
we take `N` to be that time and `b` to be that maximum cardinality. $1 ≤ b ≤ 2015$.

Let $S_t$ be the sum of heights at time $t$. The key observation is that for all $t ≥ N$
$$S_{t+1} = S_t + a_{t+1} - b$$
because 0 must be in the set of heights at time $t$ (otherwise the cardinality will increase);
this height is replaced by $a_{t+1}$ and then all $b$ balls have their height decreased by 1. Thus
$$\left|\sum_{j=m+1}^n (a_j-b)\right| = |S_n - S_m|.$$
Now for all $t ≥ N$,
$$\sum_{i=0}^{b-1} i ≤ S_t ≤ 0 + \sum_{i=0}^{b-2} (2014-i),$$
so the absolute difference is upper-bounded by
$$\sum_{i=0}^{b-2} (2014-i) - (b-1) - \sum_{i=0}^{b-2} (b-2-i) = (b-1)(2015-b) ≤ 1007^2.$$
-/


namespace Imo2015Q6

open Finset

/-- The conditions on `a` in the problem. We reindex `a` to start from 0 rather than 1;
`N` then only has to be nonnegative rather than positive, and the sum in the problem statement
is over `Ico m n` rather than `Ioc m n`. -/
def Condition (a : ℕ → ℤ) : Prop := (∀ i, a i ∈ Icc 1 2015) ∧ Function.Injective fun i ↦ i + a i

/-- The collection of ball heights in the solution. -/
def pool (a : ℕ → ℤ) : ℕ → Finset ℤ
  | 0 => ∅
  | t + 1 => (insert (a t) ((pool a t).erase 0)).map (Equiv.subRight (1 : ℤ))

variable {a : ℕ → ℤ} (ha : Condition a) {t : ℕ}

section Pool

lemma exists_add_eq_of_mem_pool {z : ℤ} (hz : z ∈ pool a t) : ∃ u < t, u + a u = t + z := by
  induction t generalizing z with
  | zero => simp only [pool, notMem_empty] at hz
  | succ t ih =>
    simp_rw [pool, mem_map, Equiv.coe_toEmbedding, Equiv.subRight_apply] at hz
    obtain ⟨y, my, ey⟩ := hz
    rw [mem_insert, mem_erase] at my; rcases my with h | h
    · use t; omega
    · obtain ⟨u, lu, hu⟩ := ih h.2
      use u; omega

include ha

/-- The ball heights are always within `[0, 2014]`. -/
lemma pool_subset_Icc : ∀ {t}, pool a t ⊆ Icc 0 2014
  | 0 => by simp [pool]
  | t + 1 => by
    intro x hx
    simp_rw [pool, mem_map, Equiv.coe_toEmbedding, Equiv.subRight_apply] at hx
    obtain ⟨y, my, ey⟩ := hx
    suffices y ∈ Icc 1 2015 by rw [mem_Icc] at this ⊢; omega
    rw [mem_insert, mem_erase] at my; rcases my with h | ⟨h₁, h₂⟩
    · exact h ▸ ha.1 t
    · have := pool_subset_Icc h₂; rw [mem_Icc] at this ⊢; omega

lemma notMem_pool_self : a t ∉ pool a t := by
  by_contra h
  obtain ⟨u, lu, hu⟩ := exists_add_eq_of_mem_pool h
  exact lu.ne (ha.2 hu)

@[deprecated (since := "2025-05-23")] alias not_mem_pool_self := notMem_pool_self

/-- The number of balls stays unchanged if there is a ball with height 0 and increases by 1
otherwise. -/
lemma card_pool_succ : #(pool a (t + 1)) = #(pool a t) + if 0 ∈ pool a t then 0 else 1 := by
  have nms : a t ∉ (pool a t).erase 0 := by
    rw [mem_erase, not_and_or]; exact .inr (notMem_pool_self ha)
  rw [pool, card_map, card_insert_of_notMem nms, card_erase_eq_ite]
  split_ifs with h
  · have := card_pos.mpr ⟨0, h⟩; omega
  · rfl

lemma monotone_card_pool : Monotone fun t ↦ #(pool a t) := by
  refine monotone_nat_of_le_succ fun t ↦ ?_
  have := card_pool_succ (t := t) ha; omega

/-- There exists a point where the number of balls reaches a maximum (which follows from its
monotonicity and boundedness). We take its coordinates for the problem's `b` and `N`. -/
lemma exists_max_card_pool : ∃ b N, ∀ t ≥ N, #(pool a t) = b :=
  converges_of_monotone_of_bounded (monotone_card_pool ha)
    (fun t ↦ by simpa using card_le_card (pool_subset_Icc ha))

end Pool

section Sums

variable {b N : ℕ} (hbN : ∀ t ≥ N, #(pool a t) = b) (ht : t ≥ N)

include ha hbN

lemma b_pos : 0 < b := by
  by_contra! h; rw [nonpos_iff_eq_zero] at h; subst h
  replace hbN : ∀ t, #(pool a t) = 0 := fun t ↦ by
    obtain h | h := le_or_gt t N
    · have : #(pool a t) ≤ #(pool a N) := monotone_card_pool ha h
      rwa [hbN _ le_rfl, nonpos_iff_eq_zero] at this
    · exact hbN _ h.le
  have cp1 : #(pool a 1) = 1 := by
    simp_rw [card_pool_succ ha, pool, card_empty, notMem_empty, ite_false]
  apply absurd (hbN 1); omega

include ht in
lemma zero_mem_pool : 0 ∈ pool a t := by
  have := card_pool_succ (t := t) ha
  have := hbN (t + 1) (by omega)
  simp_all

include ht in
/-- The key observation, one term of the telescoping sum for the problem's expression. -/
lemma sum_sub_sum_eq_sub : ∑ x ∈ pool a (t + 1), x - ∑ x ∈ pool a t, x = a t - b := by
  simp_rw [pool, sum_map, Equiv.coe_toEmbedding, Equiv.subRight_apply]
  have nms : a t ∉ (pool a t).erase 0 := by
    rw [mem_erase, not_and_or]; exact .inr (notMem_pool_self ha)
  rw [sum_insert nms, sum_erase_eq_sub (h := zero_mem_pool ha hbN ht), sum_sub_distrib, sum_const,
    nsmul_one, hbN _ ht]
  omega

/-- The telescoping sum giving the part of the problem's expression within the modulus signs. -/
lemma sum_telescope {m n : ℕ} (hm : N ≤ m) (hn : m < n) :
    ∑ j ∈ Ico m n, (a j - b) = ∑ x ∈ pool a n, x - ∑ x ∈ pool a m, x :=
  calc
    _ = ∑ j ∈ Ico m n, (∑ x ∈ pool a (j + 1), x - ∑ x ∈ pool a j, x) := by
      congr! 1 with j hj; rw [sum_sub_sum_eq_sub ha hbN]; simp at hj; omega
    _ = _ := sum_Ico_sub (∑ x ∈ pool a ·, x) hn.le

include ht in
lemma le_sum_pool : ∑ i ∈ range b, (i : ℤ) ≤ ∑ x ∈ pool a t, x := by
  convert sum_range_le_sum fun x mx ↦ (mem_Icc.mp ((pool_subset_Icc ha) mx)).1
  · rw [hbN _ ht]
  · rw [zero_add]

include ht in
lemma sum_pool_le : ∑ x ∈ pool a t, x ≤ ∑ i ∈ range (b - 1), (2014 - i : ℤ) := by
  have zmp := zero_mem_pool ha hbN ht
  rw [← insert_erase zmp, sum_insert (notMem_erase _ _), zero_add]
  convert sum_le_sum_range fun x mx ↦ ?_
  · rw [card_erase_of_mem zmp, hbN _ ht]
  · exact (mem_Icc.mp ((pool_subset_Icc ha) (mem_erase.mp mx).2)).2

end Sums

theorem result (ha : Condition a) :
    ∃ b > 0, ∃ N, ∀ m ≥ N, ∀ n > m, |∑ j ∈ Ico m n, (a j - b)| ≤ 1007 ^ 2 := by
  obtain ⟨b, N, hbN⟩ := exists_max_card_pool ha
  have bp := b_pos ha hbN
  use b, Int.natCast_pos.mpr bp, N; intro m hm n hn; rw [sum_telescope ha hbN hm hn]
  calc
    _ ≤ ∑ i ∈ range (b - 1), (2014 - i : ℤ) - ∑ i ∈ range b, (i : ℤ) :=
      abs_sub_le_of_le_of_le (le_sum_pool ha hbN (hm.trans hn.le))
        (sum_pool_le ha hbN (hm.trans hn.le)) (le_sum_pool ha hbN hm) (sum_pool_le ha hbN hm)
    _ = (b - 1) * (2015 - b) := by
      nth_rw 2 [← Nat.sub_one_add_one_eq_of_pos bp]
      rw [← sum_flip, sum_range_succ, tsub_self, Nat.cast_zero, add_zero, ← sum_sub_distrib]
      have sc : ∀ x ∈ range (b - 1), (2014 - x - (b - 1 - x : ℕ)) = (2015 - b : ℤ) := fun x mx ↦ by
        rw [mem_range] at mx; omega
      rw [sum_congr rfl sc, sum_const, card_range, nsmul_eq_mul, Nat.cast_pred bp]
    _ ≤ _ := by
      rw [← mul_le_mul_left zero_lt_four, ← mul_assoc,
        show 4 * 1007 ^ 2 = ((b - 1 : ℤ) + (2015 - b)) ^ 2 by simp]
      exact four_mul_le_sq_add ..

end Imo2015Q6
