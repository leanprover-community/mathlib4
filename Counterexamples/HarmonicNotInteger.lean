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

theorem not_int_of_not_padic_int (a : ℚ) : padicNorm 2 a >1 → a.isInt = False := by {
  intro H
  by_cases (a = 0)
  {
    rw [h] at H h
    dsimp [padicNorm] at *
    simp at H
  }
  {
    dsimp [padicNorm] at *
    sorry
  }
}

theorem harmonic_not_int : ∀ n, n ≥ 2 -> (harmonic n).isInt = False := by {
  intro n Hn
  apply not_int_of_not_padic_int

}
