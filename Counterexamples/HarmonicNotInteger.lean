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

open Rat
open BigOperators



namespace padicValRat

  /-- Ultrametric property of a p-adic valuation. -/
  lemma min_eq_padicValRat_add {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ}
  (hqr : q + r ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (hval : padicValRat p q ≠ padicValRat p r) :
  padicValRat p (q + r) = min (padicValRat p q) (padicValRat p r) := by
    have Hmin := padicValRat.min_le_padicValRat_add (p := p) (hp := hp) hqr
    wlog h : padicValRat p q < padicValRat p r generalizing q r with Hgen
    · push_neg at h; rw [add_comm, min_comm]
      exact (Hgen (by rwa [add_comm]) hr hq hval.symm
      (by rwa [min_comm,add_comm])
      (Ne.lt_of_le (Ne.symm hval) h))
    · rw [min_eq_left (le_of_lt h)] at Hmin ⊢
      suffices Hreq : padicValRat p q ≥ padicValRat p (q + r) by linarith
      suffices Haux : padicValRat p q ≥ min (padicValRat p (q + r)) (padicValRat p r) by
        rw [min_def] at Haux; split_ifs at Haux with Hspl; try assumption; linarith
      calc padicValRat p q = padicValRat p ((q + r) - r) := by congr; simp
      _ ≥ min (padicValRat p (q + r)) (padicValRat p (-r)) :=
      ge_iff_le.mp <| le_trans (padicValRat.min_le_padicValRat_add (q := q+r) (r := -r) (by simpa))
        (by rw [add_neg_cancel_right, add_sub_cancel])
      _ = min (padicValRat p (q + r)) (padicValRat p r) := by rw [padicValRat.neg]

  lemma add_eq_of_lt {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ} (hqr : q + r ≠ 0)
  (hq : q ≠ 0) (hr : r ≠ 0) (hval : padicValRat p q < padicValRat p r) :
  padicValRat p (q + r) = padicValRat p q :=
  by rw [min_eq_padicValRat_add hqr hq hr (ne_of_lt hval),min_eq_left (le_of_lt hval)]

  lemma add_lt_of_lt {p : ℕ} [hp : Fact (Nat.Prime p)] {q r₁ r₂ : ℚ} (hqr : r₁ + r₂ ≠ 0)
  (hval₁ : padicValRat p q < padicValRat p r₁) (hval₂ : padicValRat p q < padicValRat p r₂) :
   padicValRat p q < padicValRat p (r₁ + r₂) :=
   lt_of_lt_of_le (lt_min hval₁ hval₂) (padicValRat.min_le_padicValRat_add (p := p) (hp := hp) hqr)

  /--
    If the p-adic valuation of a finite set of positive rationals is greater than a given rational
    number, then the p-adic valuation of their sum is also greater than the same rational number.
  -/
  theorem finset_gen_sum_lt_of_lt {p j : ℕ} [hp : Fact (Nat.Prime p)]
  {F : ℕ → ℚ} {S : Finset ℕ} (hS : S.Nonempty)
  (hF : ∀ i, i ∈ S → padicValRat p (F j) < padicValRat p (F i))
  (hn1 : ∀ i : ℕ, 0 < F i):
  padicValRat p (F j) < padicValRat p (∑ i in S, F i) := by
    induction' hS using Finset.Nonempty.cons_induction with k s S' Hnot Hne Hind
    · rw [Finset.sum_singleton]
      exact hF k (by simp)
    · rw [Finset.cons_eq_insert, Finset.sum_insert Hnot]
      exact add_lt_of_lt
        (ne_of_gt (add_pos (hn1 s) (Finset.sum_pos (fun i _ => hn1 i) Hne)))
        (hF _ (by simp [Finset.mem_insert, true_or]))
        (Hind (fun i hi => hF _ (by rw [Finset.cons_eq_insert,Finset.mem_insert]; exact Or.inr hi)))

end padicValRat

namespace padicValNat

  lemma le_nat_log {p : ℕ} [hp : Fact (Nat.Prime p)] (n : ℕ):
    padicValNat p n ≤ Nat.log p n  := by
      by_cases (n = 0)
      · simp only [h, padicValNat.zero, Nat.log_zero_right, le_refl]
      · refine' Nat.le_log_of_pow_le (Nat.Prime.one_lt hp.elim) _
        by_contra Hnot; push_neg at Hnot
        exact h (Nat.eq_zero_of_dvd_of_lt (pow_padicValNat_dvd (p := p) (n := n)) Hnot)

  lemma le_nat_log_gen {p n₁ n₂ : ℕ} [Fact (Nat.Prime p)] (hn : n₁ ≤ n₂):
    padicValNat p n₁ ≤ Nat.log p n₂ := le_trans (le_nat_log n₁) (Nat.log_mono_right hn)

  lemma nat_log_eq_padicvalnat_iff {p : ℕ} [hp : Fact (Nat.Prime p)] (n : ℕ)(hn : 0 < n):
  Nat.log p n = padicValNat p n ↔ n < p^(padicValNat p n + 1) := by
    · rw [Nat.log_eq_iff (Or.inr ⟨(Nat.Prime.one_lt' p).out, by linarith⟩)]
      · rw [and_iff_right_iff_imp]
        exact (fun _ => Nat.le_of_dvd hn pow_padicValNat_dvd)

end padicValNat

def harmonic : ℕ → ℚ := fun n => ∑ i in Finset.range n, 1 / (i + 1)

lemma harmonic_ne_zero : ∀ n, n ≠ 0 → harmonic n > 0 := fun n Hn =>
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


lemma padicValRat_2_pow (r : ℕ)  : padicValRat 2 (1 / 2^r) = -r := by {
  rw [one_div,padicValRat.inv,neg_inj,padicValRat.pow (by simp)]
  suffices : padicValRat 2 2 = 1
  simp only [this, mul_one]
  rw [←padicValRat.self (p := 2) one_lt_two]; simp only [Nat.cast_ofNat]
}

lemma nat_log_not_dvd {n : ℕ} : ∀ i, 0 < i ∧ i ≠ 2^(Nat.log 2 n) ∧ i ≤ n → ¬ 2^(Nat.log 2 n) ∣ i := by {
  rintro i ⟨Hi₁,Hi₂,Hi₃⟩
  simp only [Nat.instDvdNat]
  push_neg
  intros c Hc
  have Hle : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by simp) n
  have Hpow : 2 ^ Nat.log 2 n * 2 = 2 ^(Nat.log 2 n + 1) := by exact rfl
  obtain ⟨k,Hk⟩ := Nat.even_or_odd' c
  by_cases (k = 0)
  {
    rw [h, mul_zero] at Hk
    rcases Hk with rfl | rfl
    linarith
    simp only [zero_add, mul_one] at Hc
    exact Hi₂ Hc
  }
  rcases Hk with rfl | rfl
  {
    rw [← mul_assoc, Hpow] at Hc
    {
      suffices Hnk : n < i by linarith
      calc n ≤ n * k := Nat.le_mul_of_pos_right (Nat.pos_of_ne_zero h)
      _ < 2^(Nat.log 2 n + 1) * k := Nat.mul_lt_mul Hle (le_refl _) (Nat.pos_of_ne_zero h)
      _ = i := Hc.symm
    }
  }
  {
    rw [mul_add, ← mul_assoc, Hpow, mul_one] at Hc
    suffices Hnk : n < i by linarith
    calc n < 2 ^ (Nat.log 2 n + 1) := Hle
    _ ≤  2 ^ (Nat.log 2 n + 1)*k := Nat.le_mul_of_pos_right (Nat.pos_of_ne_zero h)
    _ < 2 ^ (Nat.log 2 n + 1)*k + 2^ Nat.log 2 n := by linarith
    _ = i := Hc.symm
  }
  }


lemma padicValRat_ge_neg_Nat_log_ne {n : ℕ}:
∀ q, 0 < q ∧ q ≤ n → q ≠ 2^Nat.log 2 n → padicValRat 2 (1 / q) ≠ -Nat.log 2 n := by {
  rintro q ⟨Hq₁,Hq₂⟩ Hq₃
  rw [one_div,padicValRat.inv,padicValRat.of_nat]
  simp only [ne_eq, neg_inj, Nat.cast_inj]
  intro Hnot
  have := pow_padicValNat_dvd (p := 2) (n := q)
  rw [Hnot] at this
  exact nat_log_not_dvd (n := n) q ⟨Hq₁,Hq₃,Hq₂⟩ this
}

lemma padicValRat_ge_neg_Nat_log_ge {p n : ℕ}[hp : Fact (Nat.Prime p)]:
  ∀ q, q ≤ n → -Nat.log p n ≤ padicValRat p (1 / q) := by {
  intros q Hq
  rw [one_div,padicValRat.inv,padicValRat.of_nat, neg_le_neg_iff, Nat.cast_le]
  apply padicValNat.le_nat_log_gen Hq
}

lemma padicValRat_ge_neg_Nat_log_lt (n : ℕ):
∀ q, 0 < q ∧ q ≤ n → q ≠ 2^Nat.log 2 n → padicValRat 2 (1 / 2^Nat.log 2 n) < padicValRat 2 (1 / q) := by {
  rintro q ⟨Hq₁,Hq₂⟩ Hq₃
  have H₁ := padicValRat_ge_neg_Nat_log_ne q ⟨Hq₁,Hq₂⟩ Hq₃
  have H₂ := padicValRat_ge_neg_Nat_log_ge (p := 2) q Hq₂
  rw [padicValRat_2_pow]
  exact lt_of_le_of_ne H₂ H₁.symm
}

lemma pow2_log_in_finset {n : ℕ} (hn : 2 ≤ n) : 2^(Nat.log 2 n) - 1 ∈ Finset.range n := by {
    simp only [ge_iff_le, Finset.mem_range]
    have H := Nat.pow_log_le_add_one 2 n
    rw [le_iff_lt_or_eq] at H
    rcases H with H₁ | H₂
    {
      simp only [ge_iff_le, gt_iff_lt]
      refine' Nat.sub_lt_right_of_lt_add _ H₁
      calc 1 ≤ 2 := by norm_num
      _ = 2^1 := by norm_num
      _ <= 2 ^ Nat.log 2 n := by {
        refine' Nat.pow_le_pow_of_le_right (by norm_num) _
        rw [←Nat.pow_le_iff_le_log (by norm_num) _]
        simpa
        linarith
      }
    }
    have Habs : n + 1 ≤ n := by {
      rw [← H₂]
      apply Nat.pow_log_le_self; linarith
    }
    linarith
}


theorem harmonic_not_int : ∀ n, n ≥ 2 → ¬ (harmonic n).isInt := by {
  intro n Hn
  apply not_int_of_not_padic_int
  unfold padicNorm
  split_ifs with h
  {
    have := harmonic_ne_zero n
    rw [h] at this
    apply this
    linarith
  }
  {
    apply one_lt_zpow; try norm_num
    apply lt_neg.mp
    rw [neg_zero]
    suffices Hlog : padicValRat 2 (harmonic n) = -Int.log 2 (n : ℚ)
    rw [Hlog]
    simp only [Int.log_natCast, Left.neg_neg_iff, Nat.cast_pos, Nat.log_pos_iff, and_true, Hn]
    simp only [Int.log_natCast]
    rw [harmonic_singleton (pow2_log_in_finset Hn)]
    simp only [ge_iff_le, Finset.mem_range, not_lt, Finset.singleton_subset_iff, gt_iff_lt, pow_pos,
      Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat, sub_add_cancel]
    rw [padicValRat.add_eq_of_lt (p := 2) _ (one_div_ne_zero <| pow_ne_zero _ two_ne_zero) (harmonic_singleton_ne_zero (Hn)) _]; apply padicValRat_2_pow
    {
      rw [harmonic_singleton (pow2_log_in_finset Hn)] at h
      simpa only [ge_iff_le, gt_iff_lt, pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat, sub_add_cancel, Finset.mem_range, not_lt, Finset.singleton_subset_iff] using h
    }
    {
      have := @padicValRat.finset_gen_sum_lt_of_lt (p := 2) (j := 2 ^ Nat.log 2 n - 1) _ (F := fun n => 1 / ((n + 1) : ℚ)) (Finset.range n \ {2^Nat.log 2 n - 1})
      simp at *
      apply this (finset_range_sdiff_singleton_nonempty Hn)
      {
        intros i Hi₁ Hi₂
        have := padicValRat_ge_neg_Nat_log_lt (n := n) (i+1)
        simp at *
        refine' this (by linarith) _
        intro Hnot
        rw [←Hnot] at Hi₂
        simp only [ge_iff_le, add_le_iff_nonpos_left, nonpos_iff_eq_zero, add_tsub_cancel_right, not_true] at Hi₂
      }
      {
      intros i
      norm_cast; linarith
      }
    }
  }
}
