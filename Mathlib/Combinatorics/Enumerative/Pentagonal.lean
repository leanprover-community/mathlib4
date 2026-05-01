/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Int.SuccPred

/-!
# Pentagonal numbers

This file introduces (generalized) pentagonal numbers $k(3k-1)/2$ for integer $k$.

Some sources, such as A001318 in the OEIS, order generalized pentagonal numbers by indices
$k = 0, 1, -1, 2, -2, \cdots$ to form a strictly monotone sequence. This file doesn't follow this
convention, but implicitly shows the monotonicity in `pentagonal_lt_pentagonal_neg` and
`pentagonal_neg_lt_pentagonal_add_one`.

## Main definitions

* `pentagonal`: pentagonal numbers as a function `ℤ → ℕ`.

## TODO

Show the relation between pentagonal numbers and partitions, including the pentagonal number
theorem.

## References

* https://en.wikipedia.org/wiki/Pentagonal_number
-/

public section

/-- Pentagonal numbers $k(3k-1)/2$ for integer $k$. -/
def pentagonal (k : ℤ) : ℕ := (k * (3 * k - 1) / 2).toNat

theorem pentagonal_def (k : ℤ) : pentagonal k = (k * (3 * k - 1) / 2).toNat := by rfl

theorem pentagonal_neg (k : ℤ) : pentagonal (-k) = (k * (3 * k + 1) / 2).toNat := by
  grind [pentagonal_def]

theorem natCast_pentagonal (k : ℤ) : (pentagonal k : ℤ) = k * (3 * k - 1) / 2 := by
  rcases k with (_ | _) | _ <;> grind [pentagonal_def]

theorem two_mul_natCast_pentagonal (k : ℤ) : 2 * (pentagonal k : ℤ) = k * (3 * k - 1) := by
  rw [natCast_pentagonal]
  exact Int.two_mul_ediv_two_of_even (by grind)

theorem two_mul_natCast_pentagonal_neg (k : ℤ) : 2 * (pentagonal (-k) : ℤ) = k * (3 * k + 1) := by
  grind [two_mul_natCast_pentagonal]

theorem pentagonal_injective : Function.Injective pentagonal := by
  intro x y h
  replace h : (3 * (x + y) - 1) * (x - y) = 0 := by grind [two_mul_natCast_pentagonal]
  cases mul_eq_zero.mp h <;> grind

@[simp]
theorem pentagonal_inj {x y : ℤ} : pentagonal x = pentagonal y ↔ x = y :=
  pentagonal_injective.eq_iff

theorem pentagonal_lt_pentagonal_neg {k : ℤ} (h : 0 < k) : pentagonal k < pentagonal (-k) := by
  grind [natCast_pentagonal]

theorem pentagonal_neg_lt_pentagonal_add_one {k : ℤ} (h : 0 ≤ k) :
    pentagonal (-k) < pentagonal (k + 1) := by
  grind [natCast_pentagonal]

theorem pentagonal_strictMonoOn : StrictMonoOn pentagonal (Set.Ici 0) := by
  apply strictMonoOn_of_lt_add_one Set.ordConnected_Ici
  grind [natCast_pentagonal]

theorem pentagonal_strictAntiOn : StrictAntiOn pentagonal (Set.Iic 0) := by
  apply strictAntiOn_of_add_one_lt Set.ordConnected_Iic
  grind [natCast_pentagonal]

variable (R : Type*) [Ring R]

open Classical in
/-- TODO -/
noncomputable def pentagonalCoeff (n : ℕ) : R :=
  if h : ∃ k, pentagonal k = n then
    Int.negOnePow h.choose
  else
    0

theorem pentagonalCoeff_eq_zero {n : ℕ} (h : n ∉ Set.range pentagonal) :
    pentagonalCoeff R n = 0 := by
  have h : ¬ ∃ k, pentagonal k = n := by simpa using h
  simp [pentagonalCoeff, h]

@[simp]
theorem pentagonalCoeff_pentagonal (k : ℤ) :
    pentagonalCoeff R (pentagonal k) = Int.negOnePow k := by
  simp [pentagonalCoeff]
