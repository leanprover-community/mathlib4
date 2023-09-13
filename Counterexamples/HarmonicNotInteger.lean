/-
Copyright (c) 2023 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha
-/

import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal
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

  lemma min_eq_padicValRat {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ} (hqr : q + r ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
  (hval : padicValRat p q ≠ padicValRat p r) :
  padicValRat p (q + r) = min (padicValRat p q) (padicValRat p r) := by {
    have Hmin := padicValRat.min_le_padicValRat_add (p := p) (hp := hp) hqr
    wlog h : padicValRat p q < padicValRat p r generalizing q r with H
    {
      push_neg at h
      rw [add_comm, min_comm]
      refine' (H _ hr hq hval.symm _ _)
      rwa [add_comm]
      rwa [min_comm,add_comm]
      exact Ne.lt_of_le (Ne.symm hval) h
    }
    {
      rw [min_eq_left (le_of_lt h)] at Hmin ⊢
      suffices Hreq : padicValRat p q ≥ padicValRat p (q + r) by linarith
      have Haux : padicValRat p q ≥ min (padicValRat p (q + r)) (padicValRat p r) := by {
      calc padicValRat p q = padicValRat p ((q + r) - r) := by congr; simp
      _ ≥ min (padicValRat p (q + r)) (padicValRat p (-r)) := ge_iff_le.mp <| le_trans (padicValRat.min_le_padicValRat_add (q := q+r) (r := -r) (by simpa)) (by rw [add_neg_cancel_right, add_sub_cancel])
      _ = min (padicValRat p (q + r)) (padicValRat p r) := by rw [padicValRat.neg]
      }
      rw [min_def] at Haux
      split_ifs at Haux with Hspl; try assumption
      linarith
  }}

end padicValRat

namespace padicValNat

  -- TODO: prove for when strict inequality holds.
  lemma le_nat_log {p : ℕ} [hp : Fact (Nat.Prime p)] (n : ℕ):
    padicValNat p n ≤ Nat.log p n  := by {
      by_cases (n = 0); simp [h]
      apply Nat.le_log_of_pow_le (Nat.Prime.one_lt hp.elim)
      by_contra Hnot
      have H₁ := Nat.eq_zero_of_dvd_of_lt (@pow_padicValNat_dvd p n)
      push_neg at Hnot
      apply h
      apply H₁
      exact Hnot
    }

  lemma le_nat_log_gen {p n₁ n₂ : ℕ} [Fact (Nat.Prime p)] (hn : n₁ ≤ n₂):
    padicValNat p n₁ ≤ Nat.log p n₂ := le_trans (le_nat_log n₁) (Nat.log_mono_right hn)

end padicValNat

def harmonic : ℕ  → ℚ
| 0 => 0
| (k+1) => 1 / (k+1) + harmonic k

def harmonic' : ℕ → ℚ := fun n => ∑ i in Finset.range n, 1 / (i + 1)

lemma harmonic_harmonic' n : harmonic n = harmonic' n := by {
  induction' n with k ih ; try simp
  dsimp [harmonic, harmonic']
  rw [Finset.sum_range_succ, ih]
  dsimp [harmonic']
  rw [add_comm]
}

lemma harmonic_ne_zero : ∀ n, n ≠ 0 → harmonic n > 0 := by {
  intros n Hn
  induction' n with k ih; try contradiction
  dsimp [harmonic]
  by_cases (k = 0)
  {
    rw [h]
    dsimp [harmonic]
    norm_num
  }
  {
    specialize (ih h)
    have H₀ : (0 : ℚ) = 0 + 0 := by rfl
    rw [H₀]
    refine' add_lt_add _ ih
    apply div_pos; try norm_num
    norm_cast; simp only [add_pos_iff, or_true]
  }
}

theorem not_int_of_not_padic_int (a : ℚ) :
  padicNorm 2 a > 1 → ¬ a.isInt := by {
  intro H
  suffices : a.den ≠ 1; simpa [Rat.isInt]
  by_cases (a = 0)
  {
    rw [h] at H h
    dsimp [padicNorm] at *
    simp only at H
  }
  {
    dsimp [padicNorm] at *
    split_ifs at H; try contradiction
    suffices : padicValRat 2 a < 0
    unfold padicValRat at this
    intro Hden
    rw [Hden] at this
    simp only [padicValNat.one, sub_zero] at this
    norm_cast at H
    have Hz : 0 = -0 := by {norm_num}
    rw [Hz]
    apply lt_neg_of_lt_neg
    have hx : (1 : ℚ) < 2 := by {norm_num}
    rw [← zpow_lt_iff_lt hx]
    simpa only [zpow_zero]
  }
}

lemma padicValRat_2_pow (r : ℕ)  : padicValRat 2 (1 / 2^r) = -r := by {
  rw [one_div,padicValRat.inv,neg_inj,padicValRat.pow (by simp)]
  suffices : padicValRat 2 2 = 1
  simp only [this, mul_one]
  rw [←padicValRat.self (p := 2)]; simp only [Nat.cast_ofNat]
  norm_num
}

lemma padicValRat_ge_neg_Nat_log {p n : ℕ}[hp : Fact (Nat.Prime p)]: ∀ q, q ≤ n → -Nat.log p n ≤ padicValRat p (1 / q) := by {
  intros q Hq
  rw [one_div,padicValRat.inv,padicValRat.of_nat, neg_le_neg_iff, Nat.cast_le]
  apply padicValNat.le_nat_log_gen Hq
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
    apply one_lt_zpow; try simp
    apply lt_neg.mp
    rw [neg_zero]
    suffices Hlog : padicValRat 2 (harmonic n) = -Int.log 2 (n : ℚ)
    rw [Hlog]
    simp only [Int.log_natCast, Left.neg_neg_iff, Nat.cast_pos, Nat.log_pos_iff, and_true, Hn]
    simp only [Int.log_natCast]
    sorry

  }

}


-- lemma padicValRat_2_sum {r n : ℕ} (hr₁ : 2^r < n)(hr₂ : n < 2^(r+1)) : padicValRat 2 (1 / 2^r + 1 / n) = -r := by {

  -- have Hr : r = Nat.log 2 n := by {
  --   symm
  --   rw [Nat.log_eq_iff]
  --   exact ⟨le_of_lt hr₁,hr₂⟩
  --   right
  --   constructor; trivial
  --   rw [← Nat.pos_iff_ne_zero]
  --   eapply lt_of_lt_of_le _ (le_of_lt hr₁)
  --   apply pow_pos; trivial
  -- }
  -- rw [padicValRat.min_eq_padicValRat]
  -- {
  --   rw [min_eq_left]
  --   apply padicValRat_2_pow
  --   rw [padicValRat_2_pow, one_div,padicValRat.inv,padicValRat.of_nat, neg_le_neg_iff, Nat.cast_le, Hr]
  --   apply padicValNat.le_nat_log
  -- }
  -- sorry
  -- sorry
  -- sorry

  -- rw [padicValRat_2_pow, one_div, padicValRat.inv,padicValRat.of_nat]
  -- intro Hnot
  -- simp only [padicValRat.of_nat, neg_inj, Nat.cast_inj] at Hnot
  -- rw [Hnot] at hr₁
  -- have Hdvd := pow_padicValNat_dvd (p := 2) (n := n)
  -- sorry
-- }
