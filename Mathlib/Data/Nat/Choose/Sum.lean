/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Patrick Stevens
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sums of binomial coefficients

This file includes variants of the binomial theorem and other results on sums of binomial
coefficients. Theorems whose proofs depend on such sums may also go in this file for import
reasons.
-/

open Nat Finset

variable {R : Type*}

namespace Commute

variable [Semiring R] {x y : R}

/-- A version of the **binomial theorem** for commuting elements in noncommutative semirings. -/
theorem add_pow (h : Commute x y) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m := by
  let t : ℕ → ℕ → R := fun n m ↦ x ^ m * y ^ (n - m) * n.choose m
  change (x + y) ^ n = ∑ m ∈ range (n + 1), t n m
  have h_first : ∀ n, t n 0 = y ^ n := fun n ↦ by
    simp only [t, choose_zero_right, pow_zero, cast_one, mul_one, one_mul, tsub_zero]
  have h_last : ∀ n, t n n.succ = 0 := fun n ↦ by
    simp only [t, choose_succ_self, cast_zero, mul_zero]
  have h_middle :
      ∀ n i : ℕ, i ∈ range n.succ → (t n.succ i.succ) = x * t n i + y * t n i.succ := by
    intro n i h_mem
    have h_le : i ≤ n := le_of_lt_succ (mem_range.mp h_mem)
    dsimp only [t]
    rw [choose_succ_succ, cast_add, mul_add]
    congr 1
    · rw [pow_succ' x, succ_sub_succ, mul_assoc, mul_assoc, mul_assoc]
    · rw [← mul_assoc y, ← mul_assoc y, (h.symm.pow_right i.succ).eq]
      by_cases h_eq : i = n
      · rw [h_eq, choose_succ_self, cast_zero, mul_zero, mul_zero]
      · rw [succ_sub (lt_of_le_of_ne h_le h_eq)]
        rw [pow_succ' y, mul_assoc, mul_assoc, mul_assoc, mul_assoc]
  induction n with
  | zero =>
    rw [pow_zero, sum_range_succ, range_zero, sum_empty, zero_add]
    dsimp only [t]
    rw [pow_zero, pow_zero, choose_self, cast_one, mul_one, mul_one]
  | succ n ih =>
    rw [sum_range_succ', h_first, sum_congr rfl (h_middle n), sum_add_distrib, add_assoc,
      pow_succ' (x + y), ih, add_mul, mul_sum, mul_sum]
    congr 1
    rw [sum_range_succ', sum_range_succ, h_first, h_last, mul_zero, add_zero, _root_.pow_succ']

/-- A version of `Commute.add_pow` that avoids ℕ-subtraction by summing over the antidiagonal and
also with the binomial coefficient applied via scalar action of ℕ. -/
theorem add_pow' (h : Commute x y) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ antidiagonal n, n.choose m.1 • (x ^ m.1 * y ^ m.2) := by
  simp_rw [Nat.sum_antidiagonal_eq_sum_range_succ fun m p ↦ n.choose m • (x ^ m * y ^ p),
    nsmul_eq_mul, cast_comm, h.add_pow]

end Commute

/-- The **binomial theorem** -/
theorem add_pow [CommSemiring R] (x y : R) (n : ℕ) :
    (x + y) ^ n = ∑ m ∈ range (n + 1), x ^ m * y ^ (n - m) * n.choose m :=
  (Commute.all x y).add_pow n

/-- A special case of the **binomial theorem** -/
theorem sub_pow [CommRing R] (x y : R) (n : ℕ) :
    (x - y) ^ n = ∑ m ∈ range (n + 1), (-1) ^ (m + n) * x ^ m * y ^ (n - m) * n.choose m := by
  rw [sub_eq_add_neg, add_pow]
  congr! 1 with m hm
  have : (-1 : R) ^ (n - m) = (-1) ^ (n + m) := by
    rw [mem_range] at hm
    simp [show n + m = n - m + 2 * m by cutsat, pow_add]
  rw [neg_pow, this]
  ring

namespace Nat

/-- The sum of entries in a row of Pascal's triangle -/
theorem sum_range_choose (n : ℕ) : (∑ m ∈ range (n + 1), n.choose m) = 2 ^ n := by
  have := (add_pow 1 1 n).symm
  simpa [one_add_one_eq_two] using this

theorem sum_range_choose_halfway (m : ℕ) : (∑ i ∈ range (m + 1), (2 * m + 1).choose i) = 4 ^ m :=
  have : (∑ i ∈ range (m + 1), (2 * m + 1).choose (2 * m + 1 - i)) =
      ∑ i ∈ range (m + 1), (2 * m + 1).choose i :=
    sum_congr rfl fun i hi ↦ choose_symm <| by linarith [mem_range.1 hi]
  mul_right_injective₀ two_ne_zero <|
    calc
      (2 * ∑ i ∈ range (m + 1), (2 * m + 1).choose i) =
          (∑ i ∈ range (m + 1), (2 * m + 1).choose i) +
            ∑ i ∈ range (m + 1), (2 * m + 1).choose (2 * m + 1 - i) := by rw [two_mul, this]
      _ = (∑ i ∈ range (m + 1), (2 * m + 1).choose i) +
            ∑ i ∈ Ico (m + 1) (2 * m + 2), (2 * m + 1).choose i := by
        rw [range_eq_Ico, sum_Ico_reflect _ _ (by cutsat)]
        congr
        cutsat
      _ = ∑ i ∈ range (2 * m + 2), (2 * m + 1).choose i := sum_range_add_sum_Ico _ (by cutsat)
      _ = 2 ^ (2 * m + 1) := sum_range_choose (2 * m + 1)
      _ = 2 * 4 ^ m := by rw [pow_succ, pow_mul, mul_comm]; rfl

theorem choose_middle_le_pow (n : ℕ) : (2 * n + 1).choose n ≤ 4 ^ n := by
  have t : (2 * n + 1).choose n ≤ ∑ i ∈ range (n + 1), (2 * n + 1).choose i :=
    single_le_sum (fun x _ ↦ by cutsat) (self_mem_range_succ n)
  simpa [sum_range_choose_halfway n] using t

theorem four_pow_le_two_mul_add_one_mul_central_binom (n : ℕ) :
    4 ^ n ≤ (2 * n + 1) * (2 * n).choose n :=
  calc
    4 ^ n = (1 + 1) ^ (2 * n) := by simp [pow_mul]
    _ = ∑ m ∈ range (2 * n + 1), (2 * n).choose m := by simp [-Nat.reduceAdd, add_pow]
    _ ≤ ∑ _ ∈ range (2 * n + 1), (2 * n).choose (2 * n / 2) := by gcongr; apply choose_le_middle
    _ = (2 * n + 1) * choose (2 * n) n := by simp

/-- **Zhu Shijie's identity** aka hockey-stick identity, version with `Icc`. -/
theorem sum_Icc_choose (n k : ℕ) : ∑ m ∈ Icc k n, m.choose k = (n + 1).choose (k + 1) := by
  rcases lt_or_ge n k with h | h
  · rw [choose_eq_zero_of_lt (by cutsat), Icc_eq_empty_of_lt h, sum_empty]
  · induction n, h using le_induction with
    | base => simp
    | succ n _ ih =>
      rw [← Ico_insert_right (by cutsat), sum_insert (by simp), Ico_add_one_right_eq_Icc, ih,
        choose_succ_succ' (n + 1)]

/-- **Zhu Shijie's identity** aka hockey-stick identity, version with `range`.
Summing `(i + k).choose k` for `i ∈ [0, n]` gives `(n + k + 1).choose (k + 1)`.

Combinatorial interpretation: `(i + k).choose k` is the number of decompositions of `[0, i)` in
`k + 1` (possibly empty) intervals (this follows from a stars and bars description). In particular,
`(n + k + 1).choose (k + 1)` corresponds to decomposing `[0, n)` into `k + 2` intervals.
By putting away the last interval (of some length `n - i`),
we have to decompose the remaining interval `[0, i)` into `k + 1` intervals, hence the sum. -/
lemma sum_range_add_choose (n k : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (i + k).choose k = (n + k + 1).choose (k + 1) := by
  rw [← sum_Icc_choose, range_eq_Ico]
  convert (sum_map _ (addRightEmbedding k) (·.choose k)).symm using 2
  rw [map_add_right_Ico, zero_add, add_right_comm, Ico_add_one_right_eq_Icc]

end Nat

theorem Int.alternating_sum_range_choose {n : ℕ} :
    (∑ m ∈ range (n + 1), ((-1) ^ m * n.choose m : ℤ)) = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have h := add_pow (-1 : ℤ) 1 n.succ
    simp only [one_pow, mul_one, neg_add_cancel] at h
    rw [← h, zero_pow n.succ_ne_zero, if_neg n.succ_ne_zero]

theorem Int.alternating_sum_range_choose_of_ne {n : ℕ} (h0 : n ≠ 0) :
    (∑ m ∈ range (n + 1), ((-1) ^ m * n.choose m : ℤ)) = 0 := by
  rw [Int.alternating_sum_range_choose, if_neg h0]

namespace Finset

theorem sum_powerset_apply_card {α β : Type*} [AddCommMonoid α] (f : ℕ → α) {x : Finset β} :
    ∑ m ∈ x.powerset, f #m = ∑ m ∈ range (#x + 1), (#x).choose m • f m := by
  trans ∑ m ∈ range (#x + 1), ∑ j ∈ x.powerset with #j = m, f #j
  · refine (sum_fiberwise_of_maps_to ?_ _).symm
    intro y hy
    rw [mem_range, Nat.lt_succ_iff]
    rw [mem_powerset] at hy
    exact card_le_card hy
  · refine sum_congr rfl fun y _ ↦ ?_
    rw [← card_powersetCard, ← sum_const]
    refine sum_congr powersetCard_eq_filter.symm fun z hz ↦ ?_
    rw [(mem_powersetCard.1 hz).2]

theorem sum_powerset_neg_one_pow_card {α : Type*} [DecidableEq α] {x : Finset α} :
    (∑ m ∈ x.powerset, (-1 : ℤ) ^ #m) = if x = ∅ then 1 else 0 := by
  rw [sum_powerset_apply_card]
  simp only [nsmul_eq_mul', ← card_eq_zero, Int.alternating_sum_range_choose]

theorem sum_powerset_neg_one_pow_card_of_nonempty {α : Type*} {x : Finset α} (h0 : x.Nonempty) :
    (∑ m ∈ x.powerset, (-1 : ℤ) ^ #m) = 0 := by
  classical
  rw [sum_powerset_neg_one_pow_card]
  exact if_neg (nonempty_iff_ne_empty.mp h0)

variable [NonAssocSemiring R]

@[to_additive sum_choose_succ_nsmul]
theorem prod_pow_choose_succ {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    (∏ i ∈ range (n + 2), f i (n + 1 - i) ^ (n + 1).choose i) =
      (∏ i ∈ range (n + 1), f i (n + 1 - i) ^ n.choose i) *
        ∏ i ∈ range (n + 1), f (i + 1) (n - i) ^ n.choose i := by
  have A : (∏ i ∈ range (n + 1), f (i + 1) (n - i) ^ (n.choose (i + 1))) * f 0 (n + 1) =
      ∏ i ∈ range (n + 1), f i (n + 1 - i) ^ (n.choose i) := by
    rw [prod_range_succ, prod_range_succ']; simp
  rw [prod_range_succ']
  simpa [choose_succ_succ, pow_add, prod_mul_distrib, A, mul_assoc] using mul_comm _ _

@[to_additive sum_antidiagonal_choose_succ_nsmul]
theorem prod_antidiagonal_pow_choose_succ {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    (∏ ij ∈ antidiagonal (n + 1), f ij.1 ij.2 ^ (n + 1).choose ij.1) =
      (∏ ij ∈ antidiagonal n, f ij.1 (ij.2 + 1) ^ n.choose ij.1) *
        ∏ ij ∈ antidiagonal n, f (ij.1 + 1) ij.2 ^ n.choose ij.2 := by
  simp only [Nat.prod_antidiagonal_eq_prod_range_succ_mk, prod_pow_choose_succ]
  have : ∀ i ∈ range (n + 1), i ≤ n := fun i hi ↦ by simpa [Nat.lt_succ_iff] using hi
  congr 1
  · refine prod_congr rfl fun i hi ↦ ?_
    rw [tsub_add_eq_add_tsub (this _ hi)]
  · refine prod_congr rfl fun i hi ↦ ?_
    rw [choose_symm (this _ hi)]

/-- The sum of `(n+1).choose i * f i (n+1-i)` can be split into two sums at rank `n`,
respectively of `n.choose i * f i (n+1-i)` and `n.choose i * f (i+1) (n-i)`. -/
theorem sum_choose_succ_mul (f : ℕ → ℕ → R) (n : ℕ) :
    (∑ i ∈ range (n + 2), ((n + 1).choose i : R) * f i (n + 1 - i)) =
      (∑ i ∈ range (n + 1), (n.choose i : R) * f i (n + 1 - i)) +
        ∑ i ∈ range (n + 1), (n.choose i : R) * f (i + 1) (n - i) := by
  simpa only [nsmul_eq_mul] using sum_choose_succ_nsmul f n

/-- The sum along the antidiagonal of `(n+1).choose i * f i j` can be split into two sums along the
antidiagonal at rank `n`, respectively of `n.choose i * f i (j+1)` and `n.choose j * f (i+1) j`. -/
theorem sum_antidiagonal_choose_succ_mul (f : ℕ → ℕ → R) (n : ℕ) :
    (∑ ij ∈ antidiagonal (n + 1), ((n + 1).choose ij.1 : R) * f ij.1 ij.2) =
      (∑ ij ∈ antidiagonal n, (n.choose ij.1 : R) * f ij.1 (ij.2 + 1)) +
        ∑ ij ∈ antidiagonal n, (n.choose ij.2 : R) * f (ij.1 + 1) ij.2 := by
  simpa only [nsmul_eq_mul] using sum_antidiagonal_choose_succ_nsmul f n

theorem sum_antidiagonal_choose_add (d n : ℕ) :
    (∑ ij ∈ antidiagonal n, (d + ij.2).choose d) = (d + n + 1).choose (d + 1) := by
  induction n with
  | zero => simp
  | succ n hn => rw [Nat.sum_antidiagonal_succ, hn, Nat.choose_succ_succ (d + (n + 1)), ← add_assoc]

end Finset
