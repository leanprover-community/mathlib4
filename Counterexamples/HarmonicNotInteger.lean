/-
Copyright (c) 2023 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Data.Int.Log
/-!

The nth Harmonic number is not an integer. We formalize the proof using
2-adic valuations. This proof is due to K¨ursch´ak.

Reference:
https://kconrad.math.uconn.edu/blurbs/gradnumthy/padicharmonicsum.pdf

-/

namespace Counterexample


open BigOperators

/-- The nth-harmonic number defined as a finset sum of consecutive reciprocals. -/
def harmonic : ℕ → ℚ := fun n => ∑ i in Finset.range n, 1 / (i + 1)

lemma harmonic_pos : ∀ n, n ≠ 0 → 0 < harmonic n  := fun n Hn =>
  Finset.sum_pos (fun _ _ => div_pos zero_lt_one
  (by norm_cast; linarith))
  (by (rwa [Finset.nonempty_range_iff]))

lemma harmonic_singleton {n c : ℕ} (hc : c ∈ Finset.range n):
  harmonic n = 1 / (c + 1) + ∑ x in Finset.range n \ {c}, 1 / ((x : ℚ) + 1) := by
    unfold harmonic
    rwa [add_comm, Finset.sum_eq_sum_diff_singleton_add (i := c)]

lemma finset_range_sdiff_singleton_nonempty {c n : ℕ} (hn : 2 ≤ n):
  Finset.Nonempty (Finset.range n \ {c}) := by
  rw [Finset.sdiff_nonempty,Finset.subset_singleton_iff, Finset.range_eq_empty_iff,not_or]
  refine' ⟨by linarith,fun Hnot => _⟩
  suffices : n = 1; linarith
  rw [← Finset.card_range n, ← Finset.card_singleton c, Hnot]


lemma harmonic_singleton_ne_zero {c n : ℕ} (hn : 2 ≤ n) :
 (∑ x in Finset.range n \ {c}, 1 / ((x + 1 : ℚ)) ≠ 0) := by
  refine' ne_of_gt <| Finset.sum_pos (fun i _ => div_pos zero_lt_one _)
    (finset_range_sdiff_singleton_nonempty hn)
  norm_cast; simp only [add_pos_iff, or_true]

/-- If a rational is not a 2-adic integer, it is not an integer. -/
theorem not_int_of_not_padic_int {a : ℚ} (H : 1 < padicNorm 2 a):
 ¬ a.isInt := by
  suffices : a.den ≠ 1; simpa [Rat.isInt]
  by_cases (a = 0)
  · subst h; try contradiction
  · unfold padicNorm at H
    split_ifs at H; try contradiction
    suffices : padicValRat 2 a < 0; unfold padicValRat at this
    intro Hden
    rw [Hden] at this; simp only [padicValNat.one, sub_zero] at this
    norm_cast
    refine' neg_of_neg_pos _
    have hx : (1 : ℚ) < 2 := by norm_num
    rw [← zpow_lt_iff_lt hx]
    simpa only [zpow_zero]


lemma padicValRat_2_pow (r : ℕ) : padicValRat 2 (1 / 2^r) = -r := by
  rw [one_div,padicValRat.inv,neg_inj,padicValRat.pow (by simp)]
  suffices : padicValRat 2 2 = 1
  simp only [this, mul_one]
  rw [←padicValRat.self (p := 2) one_lt_two]; simp only [Nat.cast_ofNat]

/-- For `i` less than `n`, `2^Nat.log 2 n` does not divide `i` unless `i` is equal to it. -/
lemma nat_log_not_dvd {n : ℕ} :
 ∀ i, 0 < i ∧ i ≠ 2^(Nat.log 2 n) ∧ i ≤ n → ¬ 2^(Nat.log 2 n) ∣ i := by
  rintro i ⟨Hi₁,Hi₂,Hi₃⟩
  simp only [Nat.instDvdNat]
  push_neg; intros c Hc
  have Hle : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by simp) n
  have Hpow : 2 ^ Nat.log 2 n * 2 = 2 ^(Nat.log 2 n + 1) := by exact rfl
  obtain ⟨k,Hk⟩ := Nat.even_or_odd' c
  by_cases (k = 0)
  · subst h
    rw [mul_zero, zero_add] at Hk
    rcases Hk with rfl | rfl
    · linarith
    · exact Hi₂ (Hc ▸ mul_one (2^Nat.log 2 n))
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
    _ < 2 ^ (Nat.log 2 n + 1)*k + 2^ Nat.log 2 n := by linarith
    _ = i := Hc.symm

lemma padicValRat_ge_neg_Nat_log_ne {n : ℕ}:
 ∀ q, 0 < q ∧ q ≤ n → q ≠ 2^Nat.log 2 n → padicValRat 2 (1 / q) ≠ -Nat.log 2 n := by
  rintro q ⟨Hq₁,Hq₂⟩ Hq₃
  rw [one_div,padicValRat.inv,padicValRat.of_nat,ne_eq,neg_inj,Nat.cast_inj]
  exact (fun Hnot => nat_log_not_dvd (n := n) q ⟨Hq₁,Hq₃,Hq₂⟩
    (Hnot ▸ pow_padicValNat_dvd (p := 2) (n := q)))

lemma padicValRat_ge_neg_Nat_log_ge {p n : ℕ}[hp : Fact (Nat.Prime p)]:
 ∀ q, q ≤ n → -Nat.log p n ≤ padicValRat p (1 / q) := by
  intros q Hq
  rw [one_div,padicValRat.inv,padicValRat.of_nat, neg_le_neg_iff, Nat.cast_le]
  exact padicValNat.le_nat_log_gen Hq

lemma padicValRat_ge_neg_Nat_log_lt (n : ℕ):
 ∀ q, 0 < q ∧ q ≤ n → q ≠ 2^Nat.log 2 n →
  padicValRat 2 (1 / 2^Nat.log 2 n) < padicValRat 2 (1 / q) := by
  rintro q ⟨Hq₁,Hq₂⟩ Hq₃
  rw [padicValRat_2_pow]
  exact (lt_of_le_of_ne
   (padicValRat_ge_neg_Nat_log_ge (p := 2) q Hq₂)
   (padicValRat_ge_neg_Nat_log_ne q ⟨Hq₁,Hq₂⟩ Hq₃).symm)

lemma pow2_log_in_finset {n : ℕ} (hn : 2 ≤ n):
 2^(Nat.log 2 n) - 1 ∈ Finset.range n := Finset.mem_range.mpr <| lt_of_lt_of_le
 (Nat.sub_lt (pow_pos zero_lt_two _) zero_lt_one) (Nat.pow_log_le_self 2 (by linarith))

/-- The 2-adic valuation of the n-th harmonic number is the negative of the logarithm
    of n. -/
theorem harmonic_padicValRat_2 {n : ℕ} (Hn : 2 ≤ n):
 padicValRat 2 (harmonic n) = -Int.log 2 (n : ℚ) := by
  rw [Int.log_natCast,harmonic_singleton (pow2_log_in_finset Hn)]
  simp only [gt_iff_lt, pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat, sub_add_cancel]
  rw [padicValRat.add_eq_of_lt (p := 2) _ (one_div_ne_zero <| pow_ne_zero _ two_ne_zero)
  (harmonic_singleton_ne_zero (Hn)) _]; apply padicValRat_2_pow
  · have := harmonic_pos n
    rw [harmonic_singleton (pow2_log_in_finset Hn)] at this
    refine' ne_of_gt _
    simp only [ne_eq, ge_iff_le, gt_iff_lt, pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat,
      sub_add_cancel, Finset.mem_range, not_lt, Finset.singleton_subset_iff] at this
    exact (this (by linarith))
  · have := padicValRat.finset_gen_sum_lt_of_lt (p := 2) (j := 2 ^ Nat.log 2 n - 1)
      (finset_range_sdiff_singleton_nonempty Hn) (F := fun n => 1 / ((n + 1) : ℚ))
      (S := Finset.range n \ {2^Nat.log 2 n - 1})
    simp [-one_div] at *
    refine' this (fun i Hi₁ Hi₂ => _) (fun i => div_pos zero_lt_one (by norm_cast;linarith))
    · have := padicValRat_ge_neg_Nat_log_lt (n := n) (i+1)
      simp only [Nat.cast_add, Nat.cast_one] at this
      refine' this ⟨by linarith, by linarith⟩ (fun Hnot => _)
      rw [← Hnot] at Hi₂
      refine' Hi₂ _
      simp only [add_tsub_cancel_right]

/-- The n-th harmonic number is not an integer for n ≥ 2. -/
theorem harmonic_not_int : ∀ n, n ≥ 2 → ¬ (harmonic n).isInt := by
  intro n Hn
  refine' not_int_of_not_padic_int _
  dsimp [padicNorm]
  split_ifs with h
  · exfalso
    exact (ne_of_gt <| harmonic_pos n (by linarith)) h
  · refine' one_lt_zpow one_lt_two _ (lt_neg.mp _)
    rw [neg_zero, harmonic_padicValRat_2 Hn,Int.log_natCast, Left.neg_neg_iff,
     Nat.cast_pos, Nat.log_pos_iff]
    exact ⟨Hn,one_lt_two⟩
