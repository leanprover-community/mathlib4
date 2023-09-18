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

  lemma sum_eq_of_lt {p : ℕ} [hp : Fact (Nat.Prime p)] {q r : ℚ} (hqr : q + r ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
  (hval : padicValRat p q < padicValRat p r) :
  padicValRat p (q + r) = padicValRat p q := by rw [min_eq_padicValRat hqr hq hr (ne_of_lt hval),min_eq_left (le_of_lt hval)]

-- ⊢ padicValRat 2 (1 / 2 ^ Nat.log 2 n) < padicValRat 2 (∑ x in Finset.range n \ {2 ^ Nat.log 2 n - 1}, 1 / (↑x + 1))

  theorem sum_ge_of_ge {p : ℕ} [hp : Fact (Nat.Prime p)] {n j : ℕ} {F : ℕ → ℚ} (hF : ∀ i, i ≤ n → padicValRat p (F j) ≤ padicValRat p (F i)) (hn0 : ∑ i in Finset.range n, F i ≠ 0) : padicValRat p (F j) ≤ padicValRat p (∑ i in Finset.range n, F i) := by
  induction' n with d hd
  · exact False.elim (hn0 rfl)
  · rw [Finset.sum_range_succ] at hn0 ⊢
    by_cases h : ∑ x : ℕ in Finset.range d, F x = 0
    · rw [h, zero_add]
      exact hF d (by linarith)
    · refine' le_trans _ (padicValRat.min_le_padicValRat_add (p := p) hn0)
      · exact le_min (hd (fun i hi => hF _ (by linarith)) h) (hF _ (by linarith))

  theorem finset_sum_eq_of_lt {p : ℕ} [hp : Fact (Nat.Prime p)] {n j : ℕ} {F : ℕ → ℚ} (hF : ∀ i, i ≤ n → i ≠ j → padicValRat p (F j) < padicValRat p (F i)) (hn0 : ∑ i in Finset.range n, F i ≠ 0) : padicValRat p (F j) <  padicValRat p (∑ i in Finset.range n \ {j}, F i) := by
  {
    have hF' : (∀ i, i ≤ n → padicValRat p (F j) ≤ padicValRat p (F i)) := sorry
    refine' lt_of_le_of_lt (sum_ge_of_ge hF' hn0) _
    sorry
  }
  -- induction' n with d hd
  -- · exact False.elim (hn0 rfl)
  -- · rw [Finset.sum_range_succ] at hn0 ⊢
    -- by_cases h : ∑ x : ℕ in Finset.range d, F x = 0
    -- · rw [h, zero_add]
    --   exact hF d (by linarith)
    -- · refine' le_trans _ (padicValRat.min_le_padicValRat_add (p := p) hn0)
    --   · exact le_min (hd (fun i hi => hF _ (by linarith)) h) (hF _ (by linarith))

end padicValRat

namespace padicValNat

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

  lemma nat_log_eq_padicvalnat_iff {p : ℕ} [hp : Fact (Nat.Prime p)] (n : ℕ)(hn : 0 < n):
  Nat.log p n = padicValNat p n ↔ n < p^(padicValNat p n + 1) := by {
    rw [Nat.log_eq_iff]
    have Hdiv: p^padicValNat p n ≤ n := Nat.le_of_dvd hn pow_padicValNat_dvd
    simp only [and_iff_right_iff_imp, Hdiv]
    intros; trivial
    right
    refine' ⟨(Nat.Prime.one_lt' p).out,_⟩
    linarith
  }

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

lemma harmonic_singleton {n c : ℕ} (hc : c ∈ Finset.range n): harmonic n =1 / ((c + 1):ℚ) + ∑ x in Finset.range n \ {c}, 1 / ((x : ℚ) + 1) := by {
  rw [add_comm,harmonic_harmonic']
  unfold harmonic'
  rwa [Finset.sum_eq_sum_diff_singleton_add (i := c)]
}


lemma harmonic_singleton_ne_zero {c n : ℕ} (hn : 1 ≤ n)(hc : c ∈ Finset.range n) : (∑ x in Finset.range n \ {c}, 1 / ((x + 1 : ℚ)) ≠ 0) := by {
  sorry
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
    apply one_lt_zpow; try simp
    apply lt_neg.mp
    rw [neg_zero]
    suffices Hlog : padicValRat 2 (harmonic n) = -Int.log 2 (n : ℚ)
    rw [Hlog]
    simp only [Int.log_natCast, Left.neg_neg_iff, Nat.cast_pos, Nat.log_pos_iff, and_true, Hn]
    simp only [Int.log_natCast]
    rw [harmonic_singleton (pow2_log_in_finset Hn)]
    simp only [ge_iff_le, Finset.mem_range, not_lt, Finset.singleton_subset_iff, gt_iff_lt, pow_pos,
      Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat, sub_add_cancel]
    rw [padicValRat.sum_eq_of_lt (p := 2) _ (one_div_ne_zero <| pow_ne_zero _ two_ne_zero) (harmonic_singleton_ne_zero (le_trans (one_le_two) Hn) (pow2_log_in_finset Hn)) _]; apply padicValRat_2_pow
    {
      rw [harmonic_singleton (pow2_log_in_finset Hn)] at h
      simpa only [ge_iff_le, gt_iff_lt, pow_pos, Nat.cast_pred, Nat.cast_pow, Nat.cast_ofNat, sub_add_cancel, Finset.mem_range, not_lt, Finset.singleton_subset_iff] using h
    }
    {

      -- refine ?_
      sorry
    }
  }
}
