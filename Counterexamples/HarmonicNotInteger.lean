/-
Copyright (c) 2023 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha
-/

import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Data.Int.Log
/-!

The nth Harmonic number is not an integer. We formalize the proof using
2-adic valuations. This proof is due to Theisinger.

Reference:
https://kconrad.math.uconn.edu/blurbs/gradnumthy/padicharmonicsum.pdf

-/

namespace Counterexample

open Rat
open BigOperators

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


theorem harmonic_not_int : ∀ n, n ≥ 2 -> ¬ (harmonic n).isInt := by {
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
    suffices Hlog : padicValRat 2 (harmonic n) = -Nat.log 2 n
    rw [Hlog]
    simpa only [Left.neg_neg_iff, Nat.cast_pos, Nat.log_pos_iff, and_true]
    norm_cast
    sorry
  }

}
