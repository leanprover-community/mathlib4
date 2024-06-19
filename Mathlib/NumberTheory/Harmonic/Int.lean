/-
Copyright (c) 2023 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha, Thomas Browning
-/

import Mathlib.Algebra.CharP.Basic
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!

The nth Harmonic number is not an integer. We formalize the proof using
2-adic valuations. This proof is due to Kürschák.

Reference:
https://kconrad.math.uconn.edu/blurbs/gradnumthy/padicharmonicsum.pdf

-/

/-- The 2-adic valuation of the n-th harmonic number is the negative of the logarithm
    of n. -/
theorem padicValRat_two_harmonic (n : ℕ) : padicValRat 2 (harmonic n) = -Nat.log 2 n := by
  induction' n with n ih
  · simp
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [harmonic_succ]
    have key : padicValRat 2 (harmonic n) ≠ padicValRat 2 (↑(n + 1))⁻¹ := by
      rw [ih, padicValRat.inv, padicValRat.of_nat, Ne, neg_inj, Nat.cast_inj]
      exact Nat.log_ne_padicValNat_succ hn
    rw [padicValRat.add_eq_min (harmonic_succ n ▸ (harmonic_pos n.succ_ne_zero).ne')
        (harmonic_pos hn).ne' (inv_ne_zero (Nat.cast_ne_zero.mpr n.succ_ne_zero)) key, ih,
        padicValRat.inv, padicValRat.of_nat, min_neg_neg, neg_inj, ← Nat.cast_max, Nat.cast_inj]
    exact Nat.max_log_padicValNat_succ_eq_log_succ n

/-- The 2-adic norm of the n-th harmonic number is 2 raised to the logarithm of n in base 2. -/
lemma padicNorm_two_harmonic {n : ℕ} (hn : n ≠ 0) :
    ‖(harmonic n : ℚ_[2])‖ = 2 ^ (Nat.log 2 n) := by
  rw [padicNormE.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (harmonic_pos hn).ne',
    padicValRat_two_harmonic, neg_neg, zpow_natCast, Rat.cast_pow, Rat.cast_natCast, Nat.cast_ofNat]

/-- The n-th harmonic number is not an integer for n ≥ 2. -/
theorem harmonic_not_int {n : ℕ} (h : 2 ≤ n) : ¬ (harmonic n).isInt := by
  apply padicNorm.not_int_of_not_padic_int 2
  rw [padicNorm.eq_zpow_of_nonzero (harmonic_pos (ne_zero_of_lt h)).ne',
      padicValRat_two_harmonic, neg_neg, zpow_natCast]
  exact one_lt_pow one_lt_two (Nat.log_pos one_lt_two h).ne'
