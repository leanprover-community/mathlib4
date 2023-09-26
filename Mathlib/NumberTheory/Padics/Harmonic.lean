/-
Copyright (c) 2023 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Data.Int.Log
/-!

The nth Harmonic number is not an integer. We formalize the proof using
2-adic valuations. This proof is due to Kürschák.

Reference:
https://kconrad.math.uconn.edu/blurbs/gradnumthy/padicharmonicsum.pdf

-/

open BigOperators

/-- The nth-harmonic number defined as a finset sum of consecutive reciprocals. -/
def harmonic : ℕ → ℚ := fun n => ∑ i in Finset.range n, 1 / (i + 1)

lemma harmonic_pos {n : ℕ} (Hn : n ≠ 0) : 0 < harmonic n :=
  Finset.sum_pos (fun _ _ => div_pos zero_lt_one (by norm_cast; linarith))
  (by rwa [Finset.nonempty_range_iff])

lemma harmonic_singleton {n c : ℕ} (hc : c ∈ Finset.range n) :
    harmonic n = 1 / (c + 1) + ∑ x in Finset.range n \ {c}, 1 / ((x : ℚ) + 1) := by
  dsimp [harmonic]
  rwa [add_comm, Finset.sum_eq_sum_diff_singleton_add (i := c)]

lemma finset_range_sdiff_singleton_nonempty {c n : ℕ} (hn : 2 ≤ n) :
    Finset.Nonempty (Finset.range n \ {c}) := by
  rw [Finset.sdiff_nonempty, Finset.subset_singleton_iff, Finset.range_eq_empty_iff, not_or]
  refine' ⟨by linarith, fun Hnot => _⟩
  suffices n = 1 by linarith
  rw [← Finset.card_range n, ← Finset.card_singleton c, Hnot]

lemma harmonic_singleton_ne_zero {c n : ℕ} (hn : 2 ≤ n) :
    ∑ x in Finset.range n \ {c}, 1 / (x + 1 : ℚ) ≠ 0 := by
  refine' ne_of_gt <| Finset.sum_pos (fun i _ => div_pos zero_lt_one _)
    (finset_range_sdiff_singleton_nonempty hn)
  norm_cast; simp only [add_pos_iff, or_true]

lemma padicValRat_two_pow_div (r : ℕ) : padicValRat 2 (1 / 2 ^ r) = -r := by
  rw [one_div, ← padicValRat.self_pow_div (p := 2) (r := r)]
  simp only [one_div, Nat.cast_ofNat]

/-- For `i` less than `n`, `2 ^ Nat.log 2 n` does not divide `i` unless `i` is equal to it. -/
lemma nat_log_not_dvd {n i : ℕ} (Hi₁ : 0 < i) (Hi₂ : i ≠ 2 ^ Nat.log 2 n) (Hi₃ : i ≤ n) :
    ¬ 2^(Nat.log 2 n) ∣ i := by
  rintro ⟨c,Hc⟩
  have Hle : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by simp) n
  have Hpow : 2 ^ Nat.log 2 n * 2 = 2 ^ (Nat.log 2 n + 1) := by rfl
  obtain ⟨k,Hk⟩ := Nat.even_or_odd' c
  by_cases h : k = 0
  · subst h
    rw [mul_zero, zero_add] at Hk
    rcases Hk with rfl | rfl
    · linarith
    · exact Hi₂ (Hc ▸ mul_one (2 ^ Nat.log 2 n))
  rcases Hk with rfl | rfl
  · rw [← mul_assoc, Hpow] at Hc
    suffices Hnk : n < i by linarith
    calc n ≤ n * k := Nat.le_mul_of_pos_right (Nat.pos_of_ne_zero h)
    _ < 2^(Nat.log 2 n + 1) * k := Nat.mul_lt_mul Hle (le_refl _) (Nat.pos_of_ne_zero h)
    _ = i := Hc.symm
  · rw [mul_add, ← mul_assoc, Hpow, mul_one] at Hc
    suffices Hnk : n < i by linarith
    calc n < 2 ^ (Nat.log 2 n + 1) := Hle
    _ ≤  2 ^ (Nat.log 2 n + 1)*k := Nat.le_mul_of_pos_right (Nat.pos_of_ne_zero h)
    _ < 2 ^ (Nat.log 2 n + 1)*k + 2 ^ Nat.log 2 n := by linarith
    _ = i := Hc.symm

lemma padicValRat_ge_neg_nat_log_ne {n q : ℕ}(Hq₁ : 0 < q)
  (Hq₂ : q ≤ n)(Hq₃ : q ≠ 2 ^ Nat.log 2 n) :
    padicValRat 2 (1 / q) ≠ -Nat.log 2 n := by
  rw [one_div, padicValRat.inv, padicValRat.of_nat, ne_eq, neg_inj, Nat.cast_inj]
  exact (fun Hnot => nat_log_not_dvd (n := n) Hq₁ Hq₃ Hq₂
    (Hnot ▸ pow_padicValNat_dvd (p := 2) (n := q)))

lemma padicValRat_ge_neg_Nat_log_ge {p n q : ℕ}[hp : Fact (Nat.Prime p)](Hq : q ≤ n) :
    -Nat.log p n ≤ padicValRat p (1 / q) := by
  rw [one_div, padicValRat.inv, padicValRat.of_nat, neg_le_neg_iff, Nat.cast_le]
  exact le_nat_log_of_le Hq

lemma padicValRat_ge_neg_Nat_log_lt (n q : ℕ) (Hq₁ : 0 < q)
  (Hq₂ : q ≤ n) (Hq₃ : q ≠ 2 ^ Nat.log 2 n) :
    padicValRat 2 (1 / 2 ^ Nat.log 2 n) < padicValRat 2 (1 / q) := by
  rw [padicValRat_two_pow_div]
  exact (lt_of_le_of_ne
   (padicValRat_ge_neg_Nat_log_ge (p := 2) Hq₂)
   (padicValRat_ge_neg_nat_log_ne Hq₁ Hq₂ Hq₃).symm)

lemma two_pow_log_mem_range {n : ℕ} (hn : 2 ≤ n) :
    2 ^ (Nat.log 2 n) - 1 ∈ Finset.range n :=
  Finset.mem_range.mpr <| lt_of_lt_of_le (Nat.sub_lt (pow_pos zero_lt_two _) zero_lt_one)
  (Nat.pow_log_le_self 2 (by linarith))

/-- The 2-adic valuation of the n-th harmonic number is the negative of the logarithm
    of n. -/
theorem harmonic_two_adicValRat {n : ℕ} (Hn : 2 ≤ n) :
    padicValRat 2 (harmonic n) = -Int.log 2 (n : ℚ) := by
  rw [Int.log_natCast, harmonic_singleton (two_pow_log_mem_range Hn)]
  simp only [gt_iff_lt, pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat, sub_add_cancel]
  rw [padicValRat.add_eq_of_lt (p := 2) _
      (one_div_ne_zero <| pow_ne_zero _ two_ne_zero) (harmonic_singleton_ne_zero Hn) _]
  apply padicValRat_two_pow_div
  · have := harmonic_pos (n := n)
    rw [harmonic_singleton (two_pow_log_mem_range Hn)] at this
    refine' ne_of_gt _
    simp only [ne_eq, ge_iff_le, gt_iff_lt, pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat,
      sub_add_cancel, Finset.mem_range, not_lt, Finset.singleton_subset_iff] at this
    exact this (by linarith)
  · have := padicValRat.sum_gt_of_gt (p := 2) (j := 2 ^ Nat.log 2 n - 1)
      (finset_range_sdiff_singleton_nonempty Hn) (F := fun n => 1 / ((n + 1) : ℚ))
      (S := Finset.range n \ {2 ^ Nat.log 2 n - 1})
    simp only [Finset.mem_range, Finset.mem_sdiff, Finset.mem_singleton,
      Finset.singleton_subset_iff, pow_pos, Nat.cast_pred, Nat.cast_pow,
      sub_add_cancel, and_imp,gt_iff_lt] at this
    refine' this (fun i Hi₁ Hi₂ => _) (fun i => div_pos zero_lt_one (by norm_cast; linarith))
    · have := padicValRat_ge_neg_Nat_log_lt (n := n) (i+1)
      simp only [Nat.cast_add, Nat.cast_one] at this
      refine' this (by linarith) (by linarith) (fun Hnot => _)
      rw [← Hnot] at Hi₂
      refine' Hi₂ _
      simp only [add_tsub_cancel_right]

/-- The n-th harmonic number is not an integer for n ≥ 2. -/
theorem harmonic_not_int {n : ℕ} (Hn : 2 ≤ n) :
    ¬(harmonic n).isInt := by
  refine' padicNorm.not_int_of_not_padic_int 2 _
  dsimp [padicNorm]
  rw [if_neg (ne_of_gt <| harmonic_pos (by linarith))]
  refine' one_lt_zpow one_lt_two _ (lt_neg.mp _)
  rw [neg_zero, harmonic_two_adicValRat Hn,Int.log_natCast, Left.neg_neg_iff,
    Nat.cast_pos, Nat.log_pos_iff]
  exact ⟨Hn,one_lt_two⟩
