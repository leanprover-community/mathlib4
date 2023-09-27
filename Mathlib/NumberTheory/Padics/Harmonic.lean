/-
Copyright (c) 2023 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha, Thomas Browning
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
def harmonic : ℕ → ℚ := fun n => ∑ i in Finset.range n, (↑(i + 1))⁻¹

@[simp]
lemma harmonic_zero : harmonic 0 = 0 :=
  rfl

@[simp]
lemma harmonic_succ (n : ℕ) : harmonic (n + 1) = harmonic n + (↑(n + 1))⁻¹ := by
  apply Finset.sum_range_succ

lemma harmonic_pos {n : ℕ} (Hn : n ≠ 0) : 0 < harmonic n :=
  Finset.sum_pos (fun _ _ => inv_pos.mpr (by norm_cast; linarith))
  (by rwa [Finset.nonempty_range_iff])

lemma Nat.log_ne_padicValNat_succ {n : ℕ} (hn : n ≠ 0) : log 2 n ≠ padicValNat 2 (n + 1) := by
  rw [Ne, log_eq_iff (by simp [hn])]
  rintro ⟨h1, h2⟩
  rw [← lt_add_one_iff, ← mul_one (2 ^ _)] at h1
  rw [← add_one_le_iff, pow_succ] at h2
  refine' not_dvd_of_between_consec_multiples h1 (lt_of_le_of_ne' h2 _) pow_padicValNat_dvd
  exact pow_succ_padicValNat_not_dvd n.succ_ne_zero ∘ dvd_of_eq
lemma Nat.max_log_padicValNat_succ_eq_log_succ (n : ℕ) :
    max (log 2 n) (padicValNat 2 (n + 1)) = log 2 (n + 1) := by
  apply le_antisymm (max_le (le_log_of_pow_le one_lt_two (pow_log_le_add_one 2 n))
    (le_log_of_pow_le one_lt_two (le_of_dvd n.succ_pos pow_padicValNat_dvd)))
  rw [le_max_iff, or_iff_not_imp_left, not_le]
  intro h
  replace h := le_antisymm (add_one_le_iff.mpr (lt_pow_of_log_lt one_lt_two h))
    (pow_log_le_self 2 n.succ_ne_zero)
  rw [h, padicValNat.prime_pow, ← h]

/-- The 2-adic valuation of the n-th harmonic number is the negative of the logarithm
    of n. -/
theorem padicValRat_two_harmonic {n : ℕ} : padicValRat 2 (harmonic n) = -Nat.log 2 n := by
  induction' n with n ih
  · simp
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [harmonic_succ]
    have key : padicValRat 2 (harmonic n) ≠ padicValRat 2 (↑(n + 1))⁻¹
    · rw [ih, padicValRat.inv, padicValRat.of_nat, Ne, neg_inj, Nat.cast_inj]
      exact Nat.log_ne_padicValNat_succ hn
    rw [padicValRat.add_eq_min (harmonic_succ n ▸ (harmonic_pos n.succ_ne_zero).ne')
        (harmonic_pos hn).ne' (inv_ne_zero (Nat.cast_ne_zero.mpr n.succ_ne_zero)) key, ih,
        padicValRat.inv, padicValRat.of_nat, min_neg_neg, neg_inj, ← Nat.cast_max, Nat.cast_inj]
    exact Nat.max_log_padicValNat_succ_eq_log_succ n
