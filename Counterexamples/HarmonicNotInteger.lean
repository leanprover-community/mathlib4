/-
Copyright (c) 2023 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha
-/

import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!

The nth Harmonic number is not an integer. We formalize the proof using
2-adic valuations. This proof is due to Theisinger.

Reference:
https://kconrad.math.uconn.edu/blurbs/gradnumthy/padicharmonicsum.pdf

-/
open Rat

variable (p : ℕ) (x : ℤ) [Fact p.Prime]


def harmonic : ℕ  → ℚ
| 0 => 0
| (k+1) => 1 / (k+1) + harmonic k

theorem not_int_of_not_padic_int (a : ℚ) : padicNorm 2 a > 1 → ¬ a.isInt := by {
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
    simp only [padicValNat.one, CharP.cast_eq_zero, sub_zero] at this
    norm_cast
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

}
